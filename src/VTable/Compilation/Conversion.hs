
{-# LANGUAGE  BangPatterns,OverloadedStrings, StrictData #-}


{- |
        Module     : VTable.Compliation.Conversion
        Copyright  : (c) Kaya Akagi. 2018-2019
        Maintainer : akagi15@cs.dis.titech.ac.jp

        * 個票の元データから，ばらつきやエラーデータなどを除去するためにすべて，既定のデータ型に変換するためのモジュール

        * 表記を統一するために日本語を使っているので、等幅フォント推奨

        こんなことする必要がなくなるようにデータを手書きやエクセルでいじるのをやめましょう．


        * エンコーディングに関して

            > 入出力も含めてすべてUTF-8で統一する
            > Windowsでの起動は想定していないの，Dockerを利用して，Linux上で動かすこと
            > Windowsのコンソールは chcp 65001
            > Docker for Windows を利用する場合はchcp 65001をしないとTemplateHaskell部分のコンパイルが通らない．

        * その他

            > where 節内にエラーが出るので，Strict拡張は行わない
-}


module VTable.Compilation.Conversion   where

import qualified    Data.Vector                     as V
import              Data.Vector                     (Vector)
import qualified    Data.Vector.Mutable             as MV
import qualified    Data.Map.Strict                 as Map
import              Data.Map.Strict                 (Map)
import qualified    Data.Text                       as T
import              Data.Text                       (Text)
import qualified    Data.Text.IO                    as TO
import qualified    Data.List                       as L
import qualified    Data.Maybe                      as Maybe
import              Data.Semigroup
import              Data.Array.IArray
import              Data.Array.ST
import              Data.Array.IO
import              Data.Ix
import              Data.STRef
import              Data.IORef
import              GHC.Err
import              Control.Monad
import              Control.Monad.ST
import              Data.STRef
import              Data.IORef
import              Data.Either
import              Data.Char
import              System.IO
import              System.Process
import              Text.Read
import              Debug.Trace
import              Control.DeepSeq
import qualified    Data.Attoparsec.Text          as DAT
import              Data.Attoparsec.Text
import              Control.Applicative
import              Text.Show.Unicode               (ushow)
import              Control.Monad.IO.Class          (liftIO, MonadIO)
import              Control.Monad.Trans.Resource.Internal

--  for pararel
import              Control.Parallel.Strategies     hiding (parMap, (.|))
import              Control.Parallel
import qualified    Control.Monad.Parallel          as CMP

-- conduits
import              Data.Conduit
import qualified    Data.Conduit.List               as CL
import qualified    Data.Conduit.Binary             as CB hiding (sequence, dropWhile, sourceFile)
import qualified    Data.Conduit.Combinators        as CC
import qualified    Data.Text.Encoding              as E


--  Original Modules
import qualified    CSV.Text                        as CSV
import              CSV.Text
import              VTable.Data.Structure
import qualified    VTable.Data.Structure           as VDS
import              VTable.Data.Classification
import qualified    VTable.Data.Classification      as VDC

------------------------------------------------------------------
-- * General Function
------------------------------------------------------------------

-- | 固定長の数値と非固定長の数値が混ざっているのでこっちを使う
spaceDouble :: Parser Double
spaceDouble = try (many space) >> DAT.double

-- | Textの形で数値を持つものをチェックしつつ,変換する (001のような値インデックスや分類番号は数値では持てないので)
--   当てはまらない場合は,空を返す.
textToDigitText :: Text -> Text
textToDigitText tx  | T.null tx || T.all (' ' == ) tx || T.all ('　' ==) tx = T.empty
                    | otherwise  =  case (parseOnly digitText tx) of
                                    Right r       -> r
                                    Left err  -> T.empty
    where
    digitText :: Parser Text
    digitText =   many space
              >>  many digit >>= \res
              ->  return (T.pack res)

textToDouble :: Text -> Double
textToDouble tx     | T.null tx || T.all (' ' == ) tx || T.all ('　' ==) tx = 0
                    | otherwise  =  case (parseOnly spaceDouble tx) of
                                    Right r       -> r
                                    Left err  -> error $ "Can not parse Double :" ++ ushow err ++ T.unpack tx

textToValDouble :: Text -> ValDouble
textToValDouble tx  | T.null tx || T.all (' ' == ) tx || T.all ('　' ==) tx = Null
                    | otherwise  = case (parseOnly spaceDouble tx) of
                                    Right r       -> VDouble r
                                    Left err  -> error $ "Can not parse Double :" ++ ushow err  ++ T.unpack tx

doubleToVal :: Double -> ValDouble
doubleToVal db  | db == 0   =   Null
                | otherwise = VDouble db

textToInt :: Text -> Int
textToInt tx    | T.null tx || T.all (' ' == ) tx || T.all ('　' ==) tx = 0
                | otherwise  =  case (parseOnly spaceDouble tx) of
                                    Right r       -> truncate r
                                    Left err  -> error $ "Can not parse Int :" ++ ushow err ++ T.unpack tx
textToValInt :: Text -> ValInt
textToValInt tx | T.null tx || T.all (' ' == ) tx || T.all ('　' ==) tx = Null
                | otherwise  =   case (parseOnly spaceDouble tx) of
                                    Right r       -> VInt (truncate r)
                                    Left err  -> error $ "Can not parse Int :" ++ ushow err  ++ T.unpack tx

intToVal :: Int -> ValDouble
intToVal x  | x == 0    = Null
            | otherwise = VInt x


textToValCars :: [Double] -> [Text] -> ValCars
textToValCars ds tx | null ds || null tx    = Null
                    | and (map (0 == ) ds)  = Null
                    | otherwise             = VCars
                                            $! V.filter (\(Car x y)  ->  (x /= 0.0) && (not (T.null y)))
                                            $! V.fromList $! zipWith (\x y -> Car x y) ds tx


textToCars :: [Double] -> [Text] -> Cars
textToCars ds tx | null ds || null tx    = V.empty
                 | and (map (0 == ) ds)  = V.empty
                 | otherwise             =  V.filter (\(Car x y)  ->  (x /= 0.0) && (not (T.null y)))
                                         $! V.fromList $! zipWith (\x y -> Car x y) ds tx


minusToZero :: Int -> Int
minusToZero x | x <= 0    = 0
              | otherwise = x

-- | 生ﾃﾞｰﾀに入っているHeader情報
type RecordValue = Text

-- | 元ﾃﾞｰﾀのﾍｯﾀﾞーとRowを与えて指定のﾃﾞｰﾀを取ってくる
projFrom :: RecordHeader -> [RecordHeader] -> [RecordValue] -> RecordValue
projFrom hd hds tx =  case L.elemIndex hd hds of
                      Just x  -> if (length tx - 1) >= x    then (L.!!) tx x
                                                            else error $ "Can not project \""
                                                                    ++ (T.unpack hd)  ++ "\" line is too short"
                                                                    ++ ushow tx
                      Nothing -> error  $ "Can not project \""
                                        ++ (T.unpack hd)  ++ "\" in \r\n"
                                        ++ ushow hds


-- | 与えられたHeaderのデータをテキストとして取得する,
{-# INLINE getTextValues #-}
getTextValues :: [RecordHeader] -> [RecordHeader] -> [RecordValue] -> [RecordValue]
getTextValues xs hds tx = map (\x -> projFrom x hds tx) xs


-- | 与えられたHeaderのデータをテキストとして取得する,
-- 数値になりえないテキストはエラーを返す
{-# INLINE getDigitTextValues #-}
getDigitTextValues :: [RecordHeader] -> [RecordHeader] -> [RecordValue] -> [RecordValue]
getDigitTextValues xs hds tx = map (\x -> textToDigitText (projFrom x hds tx)) xs

-- | projFrom をmapしてDoubleで返す
{-# INLINE getValues #-}
getValues :: [RecordHeader] -> [RecordHeader] -> [RecordValue] -> [Double]
getValues xs hds tx = map  (\x -> textToDouble (projFrom x hds tx)) xs


-- | 調査名を商品番号に変換する test
{-# INLINE translateGoodsCodes #-}
translateGoodsCodes :: [Text] -> VDC.Thesaurus -> [Text]
translateGoodsCodes xs th = map (\x -> lookupErr x th) xs

-- ^ Headerのリスト
type HeaderTexts = [Text]

------------------------------------------------------------------
-- * 元データから,センサスデータへの変換
------------------------------------------------------------------

{- | 個別に [Text] -> Val の関数を作成しHandleで一行ずつ処理する

逐次読み込みの後一行ごとにデータを生成

データを取らない場合は,Nullを返す.
一行のデータと,そこから抜き出したいデータを指定されたときに,データを抜き出す関数
-}

{-# INLINE convert #-}
convert :: Header -> FileType -> HeaderTexts -> [Text] -> Val
convert = f
    where
    f H直轄企業コード             = fデータ変換_直轄企業コード             ; f H事業所番号                 = fデータ変換_事業所番号
    f H調査票の種類               = fデータ変換_調査票の種類               ; f H雇用情報                   = fデータ変換_雇用情報
    f H総売上                     = fデータ変換_総売上                     ; f H地域コード                 = fデータ変換_地域コード
    f H経営組織                   = fデータ変換_経営組織                   ; f H単独本所支所区分           = fデータ変換_単独本所支所区分
    f H費用等の内訳               = fデータ変換_費用等の内訳               ; f H管理補助的業務             = fデータ変換_管理補助的業務
    f H商品販売額最多部門         = fデータ変換_商品販売額最多部門         ; f H生産_鉱業_数量             = fデータ変換_生産_鉱業_数量
    f H生産_鉱業_金額             = fデータ変換_生産_鉱業_金額             ; f H生産_農林漁業_金額         = fデータ変換_生産_農林漁業_金額
    f H商品別卸売額               = fデータ変換_商品別卸売額               ; f H商品別小売額               = fデータ変換_商品別小売額
    f H事業収入_医療福祉          = fデータ変換_事業収入_医療福祉          ; f H事業所形態_医療福祉        = fデータ変換_事業所形態_医療福祉
    f H出荷額_製造業              = fデータ変換_出荷額_製造業              ; f H在庫額_製造業              = fデータ変換_在庫額_製造業
    f H収入額_加工賃              = fデータ変換_収入額_加工賃              ; f H収入額_製造業以外          = fデータ変換_収入額_製造業以外
    f H収入内訳_学校              = fデータ変換_収入内訳_学校              ; f H年初製造品在庫額           = fデータ変換_年初製造品在庫額
    f H年末製造品在庫額           = fデータ変換_年末製造品在庫額           ; f H年初半製品及び仕掛品       = fデータ変換_年初半製品及び仕掛品
    f H年末半製品及び仕掛品       = fデータ変換_年末半製品及び仕掛品       ; f H年初原材料及び燃料         = fデータ変換_年初原材料及び燃料
    f H年末原材料及び燃料         = fデータ変換_年末原材料及び燃料         ; f H商品別リース契約高         = fデータ変換_商品別リース契約高
    f H商品別レンタル売上高       = fデータ変換_商品別レンタル売上高       ; f Hレンタル総売上高           = fデータ変換_レンタル総売上高
    f Hリース年間契約高           = fデータ変換_リース年間契約高           ; f H相手先別収入割合_サB       = fデータ変換_相手先別収入割合_サB
    f H相手先別収入割合_医療福祉  = fデータ変換_相手先別収入割合_医療福祉  ; f H修理手数料収入_商業        = fデータ変換_修理手数料収入_商業
    f H仲立手数料収入_商業        = fデータ変換_仲立手数料収入_商業        ; f H商品売上原価               = fデータ変換_商品売上原価
    f H年初商品手持額             = fデータ変換_年初商品手持額             ; f H年末商品手持額             = fデータ変換_年末商品手持額
    f H年間仕入額                 = fデータ変換_年間仕入額                 ; f H対象年度                   = fデータ変換_対象年度
    f H消費税記入の別             = fデータ変換_消費税記入の別             ; f H事業別売上高               = fデータ変換_事業別売上高
    f H輸出割合                   = fデータ変換_輸出割合                   ; f H事業形態                   = fデータ変換_事業形態
    f H事前格付_事業所            = fデータ変換_事前格付_事業所            ; f H事前格付_企業              = fデータ変換_事前格付_企業
    f H産業格付                   = fデータ変換_産業格付                   ; f H信用共済事業の有無         = fデータ変換_信用共済事業の有無
    f H協同組合の種類             = fデータ変換_協同組合の種類             ; f H団体の種類                 = fデータ変換_団体の種類
    f H8時間換算雇用者数_サB      = fデータ変換_8時間換算雇用者数_サB      ; f H8時間換算雇用者数_商業     = fデータ変換_8時間換算雇用者数_商業
    f H売場面積                   = fデータ変換_売場面積                   ; f Hセルフサービス             = fデータ変換_セルフサービス
    f H開店閉店期間               = fデータ変換_開店閉店期間               ; f H販売形態                   = fデータ変換_販売形態
    f H店舗形態_商業              = fデータ変換_店舗形態_商業              ; f H商品形態                   = fデータ変換_商品形態
    f H事業収入_建サA             = fデータ変換_事業収入_建サA             ; f H工事種類                   = fデータ変換_工事種類
    f H金融業保険業の事業種類     = fデータ変換_金融業保険業の事業種類     ; f H主な事業の種類             = fデータ変換_事業の種類
    f H学校等の種類               = fデータ変換_学校等の種類               ; f H店舗形態_サB               = fデータ変換_店舗形態_サB
    f H事業収入_サB               = fデータ変換_事業収入_サB               ; f H同業者割合_サB             = fデータ変換_同業者割合
    f H原材料使用額               = fデータ変換_原材料使用額               ; f H事業所別生産物別売上高     = fデータ変換_事業所別生産物別売上高

------------------------------------------------------------------
-- ** データ抽出関数
------------------------------------------------------------------

--  以下,個別に指定されたデータを抜き出すための関数を定義していく.

------------------------------------------------------------------
-- *** H直轄企業コード
------------------------------------------------------------------

{- | 直轄企業コード
    経済センサスの調査票には，平成24，28年共に，「市区町村コード，調査区番号，事業所番号，＊コード」が記載されており，
    同一企業に属する支所等は全て同一のコードを持つ．
    この事業所コードとは別に，企業内において連番される2桁の整理番号が存在し，これらのコードを全て併せて「直轄企業コード」と呼ぶ．
    直轄企業コードは全事業所にそれぞれ固有であり，且つ，各事業所がどの企業に属するのかを判別することを可能にする．

    * S

        > [企]市区町村コード
        > [企]調査区番号
        > [企]事業所番号
        > [企]＊コード
        > [企]整理番号

    * K24 無視 S24で把握
    * K28

         > [企]市区町村コード
         > [企]調査区番号
         > [企]事業所番号
         > [企]＊コード
    * KMI28

         > (企)市区町村コード
         > (企)調査区番号
         > (企)事業所番号
         > (企)＊コード
         > (企)整理番号
    * KMP28 無視
    * 企業コード空白=0000 は単独事業所 -}

{-# INLINE fデータ変換_直轄企業コード #-}
fデータ変換_直轄企業コード :: FileType -> HeaderTexts -> [Text] -> Val
fデータ変換_直轄企業コード ft hds tx
        | getFileDep ft == S || ft == K28 = s
        | ft == KMP28                     = kmp28
        | otherwise = Null
        where
        -- 取得する列のヘッダー
        ws = L.map T.pack  [ "[企]市区町村コード"
                            , "[企]調査区番号"
                            , "[企]事業所番号"
                            , "[企]＊コード"
                            , "[企]整理番号"]

        wk = L.map T.pack  [ "(企)市区町村コード"
                            , "(企)調査区番号"
                            , "(企)事業所番号"
                            , "(企)＊コード"
                            , "(企)整理番号"]

        -- ヘッダーからインデックスを取り,値を取得
        textS = getTextValues ws hds tx
        textK = getTextValues wk hds tx

        -- 空白の場合に0で代替
        -- Kでは0000="",S では 0000="    "

        f1 x = if x == T.pack "" || x == T.pack "     " then T.pack "00000"  else x
        f2 x = if x == T.pack "" || x == T.pack "    "  then T.pack "0000"   else x
        f3 x = if x == T.pack "" || x == T.pack "    "  then T.pack "0000"   else x
        f4 x = if x == T.pack "" || x == T.pack " "     then T.pack "0"      else x
        f5 x = if x == T.pack "" || x == T.pack "  "    then T.pack "00"     else x
        fs  = [f1, f2, f3, f4,f5]

        s     = VText $ T.concat $ L.zipWith (\f x -> (f x)) fs textS
        kmp28 = VText $ T.concat $ L.zipWith (\f x -> (f x)) fs textK


------------------------------------------------------------------
--  *** H事業所番号
------------------------------------------------------------------

{- | 同一の事業所かどうかを判定するための事業所の情報

    括弧が全角と半角が混在しているので注意（S28は両方入っている．IMEで全角すべて禁止しろ）

    * S24

        > [確定]市区町村コード（所在地）
        > [確定]調査区番号（所在地）
        > [確定]事業所番号
        > [確定]＊コード

    * S28

        > [確定]市区町村コード(所在地)
        > [確定]調査区番号（所在地）
        > [確定]事業所番号
        > [確定]＊コード
    * K24

        > F15_[確定]市区町村コード（所在地）
        > F16_[確定]調査区番号（所在地）
        > F17_[確定]事業所番号
        > F18_[確定]＊コード
    * K28

        > [確定]市区町村コード(所在地)
        > [確定]調査区番号（所在地）
        > [確定]事業所番号
        > [確定]＊コード
    * KMI,KMP28

        > （28センサスキー）(確定)市区町村コード(所在地)
        > （28センサスキー）(確定)調査区番号（所在地）
        > （28センサスキー）(確定)事業所番号
        > （28センサスキー）(確定)＊コード

    * KC28,KM28
        > (確定)市区町村コード(所在地)
        > (確定)調査区番号（所在地）
        > (確定)事業所番号
        > (確定)＊コード -}

{-# INLINE fデータ変換_事業所番号 #-}
fデータ変換_事業所番号 :: FileType -> HeaderTexts -> [Text] -> Val
fデータ変換_事業所番号 ft hds tx
        | getFileDep ft == S && getFileYear ft == 24 = s24
        | getFileDep ft == S && getFileYear ft == 28 = sk28
        | ft == K24                                  = k24
        | ft == K28                                  = sk28
        | ft == KMI28                                = kmi
        | ft == KC28    || ft == KM28                = kmc
        | otherwise                                  = Null

        where
        -- 取得する列のヘッダー
        ws24 = L.map T.pack    [ "[確定]市区町村コード（所在地）"
                                , "[確定]調査区番号（所在地）"
                                , "[確定]事業所番号"
                                , "[確定]＊コード"]
        wsk28 = L.map T.pack   [ "[確定]市区町村コード(所在地)"
                                , "[確定]調査区番号（所在地）"
                                , "[確定]事業所番号"
                                , "[確定]＊コード"]
        wk24 = L.map T.pack    [ "F15_[確定]市区町村コード（所在地）"
                                , "F16_[確定]調査区番号（所在地）"
                                , "F17_[確定]事業所番号"
                                , "F18_[確定]＊コード"]
        wkmi = L.map T.pack    [ "（28センサスキー）(確定)市区町村コード(所在地)"
                                , "（28センサスキー）(確定)調査区番号（所在地）"
                                , "（28センサスキー）(確定)事業所番号"
                                , "（28センサスキー）(確定)＊コード"]
        wkmc = L.map T.pack    [ "(確定)市区町村コード(所在地)"
                                , "(確定)調査区番号（所在地）"
                                , "(確定)事業所番号"
                                , "(確定)＊コード"]

        -- ヘッダーからインデックスを取り,値を取得
        textS24   = getTextValues ws24    hds tx
        textSK28  = getTextValues wsk28   hds tx
        textK24   = getTextValues wk24    hds tx
        textKMI   = getTextValues wkmi    hds tx
        textKMC   = getTextValues wkmc    hds tx
        -- 空白の場合に0で代替
        -- Kでは0000="",S では 0000="    "
        f1 x = if x == T.pack "" || x == T.pack "     " then T.pack "00000"  else x
        f2 x = if x == T.pack "" || x == T.pack "    "  then T.pack "0000"   else x
        f3 x = if x == T.pack "" || x == T.pack "    "  then T.pack "0000"   else x
        f4 x = if x == T.pack "" || x == T.pack " "     then T.pack "0"      else x
        fs  = [f1, f2, f3, f4]

        s24   = VText $ T.concat $ L.zipWith (\f x -> (f x)) fs textS24
        sk28  = VText $ T.concat $ L.zipWith (\f x -> (f x)) fs textSK28
        k24   = VText $ T.concat $ L.zipWith (\f x -> (f x)) fs textK24
        kmi   = VText $ T.concat $ L.zipWith (\f x -> (f x)) fs textKMI
        kmc   = VText $ T.concat $ L.zipWith (\f x -> (f x)) fs textKMC


--  *** H調査票の種類
-- ----------------------------------------------------------------

-- | 調査票の種類
-- * 各年度の変換
-- * 調査票の種類を受け取って,E調査票の種類を返す関数
-- * 経産省24年は,全てまとまった情報しかない >> F31_調査票の種類 で判断する
-- * 経産省28年は無視, Sの値を使う
{-# INLINE conVKindOfQ24 #-}
conVKindOfQ24 :: Text -> Val
conVKindOfQ24 tx
    | tx == (T.pack "01") = f E単独事業所調査票  E農林漁業       E指定なし
    | tx == (T.pack "02") = f E単独事業所調査票  E鉱業           E指定なし
    | tx == (T.pack "03") = f E単独事業所調査票  E製造業         E指定なし
    | tx == (T.pack "04") = f E単独事業所調査票  E商業           E個人経営者用
    | tx == (T.pack "05") = f E単独事業所調査票  E商業           E団体法人用
    | tx == (T.pack "06") = f E単独事業所調査票  E医療福祉       E指定なし
    | tx == (T.pack "07") = f E単独事業所調査票  E学校教育       E指定なし
    | tx == (T.pack "08") = f E単独事業所調査票  E建設サービスA  E指定なし
    | tx == (T.pack "09") = f E単独事業所調査票  E協同組合       E指定なし
    | tx == (T.pack "1")  = f E単独事業所調査票  E農林漁業       E指定なし
    | tx == (T.pack "2")  = f E単独事業所調査票  E鉱業           E指定なし
    | tx == (T.pack "3")  = f E単独事業所調査票  E製造業         E指定なし
    | tx == (T.pack "4")  = f E単独事業所調査票  E商業           E個人経営者用
    | tx == (T.pack "5")  = f E単独事業所調査票  E商業           E団体法人用
    | tx == (T.pack "6")  = f E単独事業所調査票  E医療福祉       E指定なし
    | tx == (T.pack "7")  = f E単独事業所調査票  E学校教育       E指定なし
    | tx == (T.pack "8")  = f E単独事業所調査票  E建設サービスA  E指定なし
    | tx == (T.pack "9")  = f E単独事業所調査票  E協同組合       E指定なし
    | tx == (T.pack "10") = f E単独事業所調査票  EサービスB      E個人経営者用
    | tx == (T.pack "11") = f E単独事業所調査票  EサービスB      E団体法人用
    | tx == (T.pack "12") = f E産業共通調査票    E産業なし       E指定なし
    | tx == (T.pack "13") = f E企業調査票        E産業なし       E指定なし
    | tx == (T.pack "14") = f E企業調査票        E学校教育       E指定なし
    | tx == (T.pack "15") = f E企業調査票        E建設サービスA  E指定なし
    | tx == (T.pack "16") = f E事業所調査票      E農林漁業       E指定なし
    | tx == (T.pack "17") = f E事業所調査票      E鉱業           E指定なし
    | tx == (T.pack "18") = f E事業所調査票      E製造業         E指定なし
    | tx == (T.pack "19") = f E事業所調査票      E商業           E指定なし
    | tx == (T.pack "20") = f E事業所調査票      E医療福祉       E指定なし
    | tx == (T.pack "21") = f E事業所調査票      E学校教育       E指定なし
    | tx == (T.pack "22") = f E事業所調査票      E建設サービスA  E指定なし
    | tx == (T.pack "23") = f E事業所調査票      E協同組合       E指定なし
    | tx == (T.pack "24") = f E事業所調査票      EサービスB      E指定なし
    | T.null tx           = Null
    | tx == (T.pack " ")  = Null
    | tx  == T.pack "  "  = Null -- 邪悪すぎる
    | otherwise           = error $ "conVKindOfQ24: " ++ ushow tx
    where f x y z = V調査票の種類 $ E調査票の種類 x y z
{-# INLINE conVKindOfQ28 #-}
conVKindOfQ28 :: Text -> Val
conVKindOfQ28 tx
    | tx == "01" = f E個人経営調査票        E産業なし           E指定なし
    | tx == "02" = f E単独事業所調査票      E農林漁業           E指定なし
    | tx == "03" = f E単独事業所調査票      E鉱業               E指定なし
    | tx == "04" = f E単独事業所調査票      E製造業             E指定なし
    | tx == "05" = f E単独事業所調査票      E商業               E指定なし
    | tx == "06" = f E単独事業所調査票      E医療福祉           E指定なし
    | tx == "07" = f E単独事業所調査票      E建設サービスA学校  E指定なし
    | tx == "08" = f E単独事業所調査票      E協同組合           E指定なし
    | tx == "09" = f E単独事業所調査票      EサービスB          E指定なし
    | tx == "1"  = f E個人経営調査票        E産業なし           E指定なし
    | tx == "2"  = f E単独事業所調査票      E農林漁業           E指定なし
    | tx == "3"  = f E単独事業所調査票      E鉱業               E指定なし
    | tx == "4"  = f E単独事業所調査票      E製造業             E指定なし
    | tx == "5"  = f E単独事業所調査票      E商業               E指定なし
    | tx == "6"  = f E単独事業所調査票      E医療福祉           E指定なし
    | tx == "7"  = f E単独事業所調査票      E建設サービスA学校  E指定なし
    | tx == "8"  = f E単独事業所調査票      E協同組合           E指定なし
    | tx == "9"  = f E単独事業所調査票      EサービスB          E指定なし
    | tx == "10" = f E単独事業所調査票      E団体               E指定なし
    | tx == "11" = f E産業共通調査票        E産業なし           E指定なし
    | tx == "12" = f E企業調査票            E産業なし           E指定なし
    | tx == "13" = f E企業調査票            E建設サービスA学校  E指定なし
    | tx == "14" = f E団体調査票            E団体               E指定なし
    | tx == "15" = f E事業所調査票          E農林漁業           E指定なし
    | tx == "16" = f E事業所調査票          E鉱業               E指定なし
    | tx == "17" = f E事業所調査票          E製造業             E指定なし
    | tx == "18" = f E事業所調査票          E商業               E指定なし
    | tx == "19" = f E事業所調査票          E医療福祉           E指定なし
    | tx == "20" = f E事業所調査票          E建設サービスA学校  E指定なし
    | tx == "21" = f E事業所調査票          E協同組合           E指定なし
    | tx == "22" = f E事業所調査票          EサービスB          E指定なし
    | tx == "23" = f E事業所調査票          E団体               E指定なし
    | T.null tx           = Null
    | tx == (T.pack " ")  = Null
    | tx  == T.pack "  "  = Null -- 邪悪すぎる
    | otherwise           = error $ "conVKindOfQ28: " ++ ushow tx
    where f x y z = V調査票の種類 $ E調査票の種類 x y z

-- | ファイルの種類と,ヘッダーを受け取って,調査票の種類を返す
-- * 24年だけ 調査票の種類,28年は調査票の種別
{-# INLINE fデータ変換_調査票の種類 #-}
fデータ変換_調査票の種類 :: FileType -> HeaderTexts -> [Text] -> Val
fデータ変換_調査票の種類 ft hds tx
        | ft == K24                                  = k24
        | getFileYear ft == 24 && getFileDep ft == S = s24
        | getFileYear ft == 28 && getFileDep ft == S = s28
        | otherwise                                  = Null
        where
        -- 取得する列のヘッダー
        ws24 = T.pack "調査票の種類"
        ws28 = T.pack "調査票の種別"
        wk24 = T.pack "F31_調査票の種類"
        -- ヘッダーからインデックスを取り,値を取得
        s24text = projFrom ws24 hds tx
        s28text = projFrom ws28 hds tx
        k24text = projFrom wk24 hds tx
        --
        s24 = conVKindOfQ24 s24text
        s28 = conVKindOfQ28 s28text
        k24 = conVKindOfQ24 k24text

--  *** H総売上
-- ----------------------------------------------------------------

-- | S28 ［集計用］売上（収入）金額
-- * S24 [集]売上（収入）金額
-- * K24 F1783_[集]売上（収入）金額
-- * K28 ［集計用］売上（収入）金額
{-# INLINE fデータ変換_総売上 #-}
fデータ変換_総売上 :: FileType -> HeaderTexts -> [Text] -> Val
fデータ変換_総売上 ft hds tx
    | getFileYear ft == 24 && getFileDep ft == S = s24
    | getFileYear ft == 28 && getFileDep ft == S = s28
    | getFileYear ft == 24 && getFileDep ft == K = k24
    | ft == K28 = k28
    | otherwise = Null
    where
        -- 取得する列のヘッダー
        ws24 = T.pack "[集]売上（収入）金額"
        ws28 = T.pack "［集計用］売上（収入）金額"
        wk24 = T.pack "F1783_[集]売上（収入）金額"
        wk28 = T.pack "［集計用］売上（収入）金額"
        -- ヘッダーからインデックスを取り,値を取得
        s24text = projFrom ws24 hds tx; s28text = projFrom ws28 hds tx
        k24text = projFrom wk24 hds tx; k28text = projFrom wk28 hds tx
        --

        s24 = textToValDouble s24text
        s28 = textToValDouble s28text
        k24 = textToValDouble k24text
        k28 = textToValDouble k28text


--  *** H地域コード
-- ----------------------------------------------------------------

{-| 地域コード

    > S24 [確定]市区町村コード（所在地） 五桁の番号 28年とは括弧が異なる
    > S28 [確定]市区町村コード(所在地) 五桁の番号
    > K24 F15_[確定]市区町村コード（所在地） 五桁の番号
    > K28 [確定]市区町村コード(所在地)
    > KMI28 市区町村番号（表記上）
    > KMP28 （28センサスキー）(確定)市区町村コード(所在地)
    > KC28 KM28   (確定)市区町村コード(所在地)


    見事に全部違って素敵ですね．

    * いずれもはじめが01の場合は4桁   -}
{-# INLINE fデータ変換_地域コード#-}
fデータ変換_地域コード :: FileType -> HeaderTexts -> [Text] -> ValText
fデータ変換_地域コード ft hds tx
    | getFileYear ft == 24 && getFileDep ft == S = s24
    | getFileYear ft == 28 && getFileDep ft == S = ks28
    | ft == K24                                  = k24
    | ft == K28                                  = ks28
    | ft == KMI28                                = kmi28
    | ft == KMP28                                = kmp28
    | otherwise                                  = oth
    where
        -- 取得する列のヘッダー
        ws24    = T.pack "[確定]市区町村コード（所在地）"
        wk24    = T.pack "F15_[確定]市区町村コード（所在地）"
        wkmi28  = T.pack "市区町村番号（表記上）"
        wkmp28  = T.pack "（28センサスキー）(確定)市区町村コード(所在地)"
        wks28   = T.pack "[確定]市区町村コード(所在地)"
        woth    = T.pack "(確定)市区町村コード(所在地)"

        -- ヘッダーからインデックスを取り,値を取得
        s24text    = projFrom ws24   hds tx
        k24text    = projFrom wk24   hds tx
        kmi28text  = projFrom wkmi28 hds tx
        kmp28text  = projFrom wkmp28 hds tx
        ks28text   = projFrom wks28  hds tx
        othtext    = projFrom woth   hds tx

        -- 4桁の場合先頭に0を足す
        f :: Text -> Val
        f tx    | T.null tx        = Null
                | T.length tx <= 1 = Null
                | T.length tx == 4 = VText $ T.cons '0' tx
                | otherwise        = VText tx

        s24   = f s24text
        k24   = f k24text
        kmi28 = f kmi28text
        kmp28 = f kmp28text
        ks28  = f ks28text
        oth   = f othtext


--  *** H経営組織
-- ----------------------------------------------------------------

-- | * S24 28 経営組織
-- * K24 F104_経営組織
-- * K28 値がないので無視
{-# INLINE fデータ変換_経営組織 #-}
fデータ変換_経営組織 :: FileType -> HeaderTexts -> [Text] -> Val
fデータ変換_経営組織 ft hds tx
    | getFileYear ft == 24 && getFileDep ft == K = k24
    | getFileYear ft == 28 && getFileDep ft == K = Null
    | otherwise                                  = oth
    where
        -- 取得する列のヘッダー
        wk24  = T.pack "F104_経営組織"
        woth  = T.pack  "経営組織"
        -- ヘッダーからインデックスを取り,値を取得
        k24text = projFrom wk24 hds tx
        othtext = projFrom woth hds tx
        -- 4桁の場合先頭に0を足す
        f :: Text -> Val
        f tx    | tx  == T.pack "1" = V経営組織 E個人経営
                | tx  == T.pack "2" = V経営組織 E株式会社
                | tx  == T.pack "3" = V経営組織 E合名会社
                | tx  == T.pack "4" = V経営組織 E合同会社
                | tx  == T.pack "5" = V経営組織 E会社以外の法人
                | tx  == T.pack "6" = V経営組織 E外国の会社
                | tx  == T.pack "7" = V経営組織 E法人でない団体
                | T.null tx         = Null
                | tx  == T.pack " " = Null -- まぎれてる
                | otherwise         = error $ "fデータ変換_経営組織 f 予期しない文字列" ++ ushow tx

        k24 = f k24text
        oth = f othtext

--  *** H単独本所支所区分
-----------------------------------------------------------

-- | S24 [事]単独・本所・支所3区分
--
-- S28 ［事］単独・本所・支所３区分
--
-- k24 F2024_[事]単独・本所・支所3区分
--
-- k28 ［事］単独・本所・支所３区分

{-# INLINE fデータ変換_単独本所支所区分 #-}
fデータ変換_単独本所支所区分 :: FileType -> HeaderTexts -> [Text] -> Val
fデータ変換_単独本所支所区分 ft hds tx
    | getFileYear ft == 24 && getFileDep ft == S = s24
    | getFileYear ft == 28 && getFileDep ft == S = s28
    | getFileYear ft == 24 && getFileDep ft == K = k24
    | ft == K28 = k28
    | otherwise = Null
    where
        -- 取得する列のヘッダー
        ws24 = T.pack "[事]単独・本所・支所3区分"
        ws28 = T.pack "［事］単独・本所・支所３区分"
        wk24 = T.pack "F2024_[事]単独・本所・支所3区分"
        wk28 = T.pack "［事］単独・本所・支所３区分"
        -- ヘッダーからインデックスを取り,値を取得

        s24text = projFrom ws24 hds tx
        s28text = projFrom ws28 hds tx
        k24text = projFrom wk24 hds tx
        k28text = projFrom wk28 hds tx
        --
        f tx    | T.pack "1" == tx    = V単独本所支所区分 E単独事業所
                | T.pack "2" == tx    = V単独本所支所区分 E本所
                | T.pack "3" == tx    = V単独本所支所区分 E支所
                | T.null tx           = Null
                | T.pack " " == tx    = Null
                | tx  == T.pack "  "  = Null
                | otherwise        = error $ "fデータ変換_単独本所支所区分" ++ ushow tx

        s24 = f s24text
        s28 = f s28text
        k24 = f k24text
        k28 = f k28text

--  *** H雇用情報
-- ----------------------------------------------------------------

{- | 個人業主,事業従業者数,雇用者数がわかれば取り敢えず良い
    * S24

    >    [企]㈰個人業主（男女計）
    >    [企]㈯従業者合計（男女計）
    >    [企]㉀うち別経営への出向・派遣者（男女計）
    >    [企]常用雇用者数（男女計）
    >    [事]㈰個人業主（男女計）
    >    [事]㈯従業者合計（男女計）
    >    [事]㉀うち別経営への出向・派遣者（男女計）
    >    [事]常用雇用者数（男女計）
    * S28

    >    ［企］１個人業主（男女計）
    >    ［企］７従業者合計（男女計）
    >    ［企］８うち別経営への出向・派遣者（男女計）
    >    ［企］常用雇用者数（男女計）
    >    ［事］１個人業主（男女計）
    >    ［事］７従業者合計（男女計）
    >    ［事］８うち別経営への出向・派遣者（男女計）
    >    ［事］常用雇用者数（男女計）
    * k24

    >    F1570_[企]雇用者数（男女計）
    >    F1616_[企]事業従事者数（男女計）
    >    F1670_[事]㈰個人業主（男女計）
    >    F1683_[事]常用雇用者数（男女計）
    >    F1684_[事]雇用者数（男女計）
    >    F1686_[事]事業従事者数（男女計）
    * k28

    >    ［企］１個人業主（男女計）
    >    ［企］雇用者数（男女計）
    >    ［企］事業従事者数（男女計）
    >    ［事］１個人業主（男女計）
    >    ［事］雇用者数（男女計）
    >    ［事］事業従事者（男女計）-}
{-# INLINE fデータ変換_雇用情報 #-}
fデータ変換_雇用情報 :: FileType -> HeaderTexts -> [Text] -> Val
fデータ変換_雇用情報 ft hds tx
    | getFileYear ft == 24 && getFileDep ft == S = s24
    | getFileYear ft == 28 && getFileDep ft == S = s28
    | getFileYear ft == 24 && getFileDep ft == K = k24
    | ft == K28                                  = k28
    | otherwise                                  = Null
    where
        -- 取得する列のヘッダー
        ws24 = L.map T.pack    [ "[企]①個人業主（男女計）"
                                , "[企]⑦従業者合計（男女計）"
                                , "[企]⑧うち別経営への出向・派遣者（男女計）"
                                , "[企]常用雇用者数（男女計）"
                                , "[事]①個人業主（男女計）"
                                , "[事]⑦従業者合計（男女計）"
                                , "[事]⑧うち別経営への出向・派遣者（男女計）"
                                , "[事]常用雇用者数（男女計）"]
        ws28 = L.map T.pack    [ "［企］１個人業主（男女計）"
                                , "［企］７従業者合計（男女計）"
                                , "［企］８うち別経営への出向・派遣者（男女計）"
                                , "［企］常用雇用者数（男女計）"
                                , "［事］１個人業主（男女計）"
                                , "［事］７従業者合計（男女計）"
                                , "［事］８うち別経営への出向・派遣者（男女計）"
                                , "［事］常用雇用者数（男女計）"]

        wk24 = L.map T.pack    [ "F1670_[事]①個人業主（男女計）"
                                , "F1570_[企]雇用者数（男女計）"
                                , "F1616_[企]事業従事者数（男女計）"
                                , "F1670_[事]①個人業主（男女計）"
                                , "F1684_[事]雇用者数（男女計）"
                                , "F1686_[事]事業従事者数（男女計）"]

        wk28 = L.map T.pack    [  "［企］１個人業主（男女計）"
                                ,  "［企］雇用者数（男女計）"
                                ,  "［企］事業従事者数（男女計）"
                                ,  "［事］１個人業主（男女計）"
                                ,  "［事］雇用者数（男女計）"
                                ,  "［事］事業従事者（男女計）"]

        -- ヘッダーからインデックスを取り,値を取得
        s24text = map (\x -> textToInt (projFrom x hds tx)) ws24
        s28text = map (\x -> textToInt (projFrom x hds tx)) ws28
        k24text = map (\x -> textToInt (projFrom x hds tx)) wk24
        k28text = map (\x -> textToInt (projFrom x hds tx)) wk28

        --

        -- Error
        -- 結構マイナスになる組み合わせがあるので引き算するときは
        -- minusToZero かます．

        f :: [Int] -> Val
        f xs    | and (map (0== ) xs) = Null
                | L.length xs == 8  = V雇用情報
                                    $ E雇用情報 { _企雇用者数     =   xs !! 3
                                                , _企個人事業主   =   xs !! 0
                                                , _企事業従業者数 = minusToZero (( xs !! 1 ) - (xs !! 2))
                                                , _事雇用者数     =   xs !! 7
                                                , _事個人事業主   =   xs !! 4
                                                , _事事業従業者数 = minusToZero (( xs !! 5 ) - (xs !! 6))}
                | L.length xs == 6  = V雇用情報
                                    $ E雇用情報 { _企雇用者数     =   xs !! 1
                                                , _企個人事業主   =   xs !! 0
                                                , _企事業従業者数 =   xs !! 2
                                                , _事雇用者数     =   xs !! 4
                                                , _事個人事業主   =   xs !! 3
                                                , _事事業従業者数 =   xs !! 5}

        s24 = f s24text
        s28 = f s28text
        k24 = f k24text
        k28 = f k28text

--  *** H費用等の内訳
-- ----------------------------------------------------------------

{- | 費用等の内訳
    * S24

        > ②費用総額・経常費用
        > ③うち売上原価
        > ④給与総額
        > ⑤福利厚生費(退職金含む)
        > ⑥動産・不動産賃借料
        > ⑦減価償却費
        > ⑧租税公課(法人_住民_事業税除く)
        > ⑨外注費
        > ⑩支払利息等
    * S28

        >    補正＿２費用総額（売上原価・販売費及び一般管理費）
        >    補正＿３うち売上原価
        >    補正＿４給与総額
        >    補正＿５福利厚生費（退職金を含む）
        >    補正＿６動産・不動産賃借料
        >    補正＿７減価償却費
        >    補正＿８租税公課（法人税、住民税、事業税を除く）
        >    補正＿９外注費
        >    補正＿１０支払利息等
    * k24

        >    F1321_㈪費用総額・経常費用
        >    F1322_㈫うち売上原価
        >    F1323_㈬給与総額
        >    F1324_㈭福利厚生費(退職金含む)
        >    F1325_㈮動産・不動産賃借料
        >    F1326_㈯減価償却費
        >    F1327_㉀租税公課(法人_住民_事業税除く)
        >    F1328_㈷外注費
        >    F1329_㉂支払利息等
    * k28

        >    補正＿２費用総額（売上原価・販売費及び一般管理費）
        >    補正＿３うち売上原価
        >    補正＿４給与総額
        >    補正＿５福利厚生費（退職金を含む）
        >    補正＿６動産・不動産賃借料
        >    補正＿７減価償却費
        >    補正＿８租税公課（法人税、住民税、事業税を除く）
        >    補正＿９外注費
        >    補正＿１０支払利息等
    * k28個別 無視
-}
{-# INLINE fデータ変換_費用等の内訳 #-}
fデータ変換_費用等の内訳 :: FileType -> HeaderTexts -> [Text] -> ValCars
fデータ変換_費用等の内訳 ft hds tx
    | getFileYear ft == 24 && getFileDep ft == S = s24
    | getFileYear ft == 28 && getFileDep ft == S = s28
    | getFileYear ft == 24 && getFileDep ft == K = k24
    | ft == K28                                  = k28
    | otherwise                                  = Null
    where
        -- 取得する列のヘッダー
        ws24  = L.map T.pack   [ "②費用総額・経常費用"
                                , "③うち売上原価"
                                , "④給与総額"
                                , "⑤福利厚生費(退職金含む)"
                                , "⑥動産・不動産賃借料"
                                , "⑦減価償却費"
                                , "⑧租税公課(法人_住民_事業税除く)"
                                , "⑨外注費"
                                , "⑩支払利息等"]
        ws28  = L.map T.pack   [ "補正＿２費用総額（売上原価・販売費及び一般管理費）"
                                ,  "補正＿３うち売上原価"
                                ,  "補正＿４給与総額"
                                ,  "補正＿５福利厚生費（退職金を含む）"
                                ,  "補正＿６動産・不動産賃借料"
                                ,  "補正＿７減価償却費"
                                ,  "補正＿８租税公課（法人税、住民税、事業税を除く）"
                                ,  "補正＿９外注費"
                                ,  "補正＿１０支払利息等"]
        wk24  = L.map T.pack   [ "F1321_②費用総額・経常費用"
                                , "F1322_③うち売上原価"
                                , "F1323_④給与総額"
                                , "F1324_⑤福利厚生費(退職金含む)"
                                , "F1325_⑥動産・不動産賃借料"
                                , "F1326_⑦減価償却費"
                                , "F1327_⑧租税公課(法人_住民_事業税除く)"
                                , "F1328_⑨外注費"
                                , "F1329_⑩支払利息等"]
        wk28   = L.map T.pack  [ "補正＿２費用総額（売上原価・販売費及び一般管理費）"
                                , "補正＿３うち売上原価"
                                , "補正＿４給与総額"
                                , "補正＿５福利厚生費（退職金を含む）"
                                , "補正＿６動産・不動産賃借料"
                                , "補正＿７減価償却費"
                                , "補正＿８租税公課（法人税、住民税、事業税を除く）"
                                , "補正＿９外注費"
                                , "補正＿１０支払利息等"]

        -- ヘッダーからインデックスを取り,値を取得
        s24text = map (\x -> textToDouble (projFrom x hds tx)) ws24
        s28text = map (\x -> textToDouble (projFrom x hds tx)) ws28
        k24text = map (\x -> textToDouble (projFrom x hds tx)) wk24
        k28text = map (\x -> textToDouble (projFrom x hds tx)) wk28

        --
        f :: [Double] -> Val
        f xs | and (map (0 == ) xs) = Null
             | otherwise = VCars $ V.fromList
                                 $ zipWith (\x y -> Car x (T.pack y)) xs
                                [ "費用総額", "売上原価"
                                , "給与総額", "福利厚生費"
                                , "動産不動産賃借料"
                                , "減価償却費", "租税公課"
                                , "外注費", "支払利息"]
        s24 = f s24text
        s28 = f s28text
        k24 = f k24text
        k28 = f k28text


--  *** 管理補助的業務
-- ---------------------------------------------------------

{- |
    * S 管理・補助的業務
    * K 該当項目なし
-}
{-# INLINE fデータ変換_管理補助的業務 #-}
fデータ変換_管理補助的業務 :: FileType -> HeaderTexts -> [Text] -> Val管理補助的業務
fデータ変換_管理補助的業務 ft hds tx
    |  getFileDep ft == S = result
    |  otherwise          = Null
    where

    ws      = T.pack "管理・補助的業務"
    sTexs   = projFrom ws hds tx

    f tx    | T.pack "1" == tx      = V管理補助的業務 E管理補助的業務
            | T.pack "2" == tx      = V管理補助的業務 E補助的業務
            | T.pack "3" == tx      = V管理補助的業務 E自家用倉庫
            | T.null tx             = Null
            | T.pack " " == tx      = Null
            | tx  == T.pack "  "    = Null
            | otherwise        = error $ "fデータ変換_管理補助的業務 f 予期しない文字列: " ++ ushow tx

    result = f sTexs

--  *** H商品販売額最多部門
------------------------------------------------------------------

-- | * S 無視
--   * k24  F954_卸売部門又は小売部門の別
--   * k28  無視
--   * KC28 卸売部門又は小売部門の別
--   * KM,KMI,KMP 項目なし

{-# INLINE fデータ変換_商品販売額最多部門 #-}
fデータ変換_商品販売額最多部門 :: FileType -> HeaderTexts -> [Text] -> Val商品販売額最多部門
fデータ変換_商品販売額最多部門 ft hds tx
    | getFileYear ft == 24 && getFileDep ft == K = k24
    | getFileYear ft == 28 && getFileDep ft == K && getFileInd ft == E商業 = k28
    | otherwise                                                            = Null
    where
        -- 取得する列のヘッダー
        w0k24 = T.pack "F954_卸売部門又は小売部門の別"
        w0k28 = T.pack "卸売部門又は小売部門の別"

        -- ヘッダーからインデックスを取り,値を取得

        k24text = projFrom w0k24 hds tx
        k28text = projFrom w0k28 hds tx
        --
        f :: Text -> Val
        f tx | T.pack "1" == tx     = V商品販売額最多部門 E卸売
             | T.pack "2" == tx     = V商品販売額最多部門 E小売
             | T.null tx            = Null
             | T.pack " " == tx     = Null
             | tx  == T.pack "  "   = Null
             | otherwise         = error $ "fデータ変換_商品販売額最多部門 f 予期しない文字列: " ++ ushow tx

        k24 = f k24text
        k28 = f k28text

--  *** H生産_鉱業_数量
-- ----------------------------------------------------------------

{- |
    - S無視
    - K24

        >   F383_111金鉱（精含量）ｇ
        >   F384_112銀鉱（精含量）ｋｇ
        >   F385_121鉛鉱（精含量）ｔ
        >   F386_122亜鉛鉱（精含量）ｔ
        >   F387_131鉄鉱（精含量）ｔ
        >   F388_191銅鉱（精含量）ｔ
        >   F389_211石炭（精炭）ｔ
        >   F390_221亜炭（精炭）ｔ
        >   F391_311原油ｋｌ
        >   F392_321天然ガス（基準状態）千_
        >   F393_411花こう岩・同類似岩石（製品）ｔ
        >   F394_421石英粗面岩・同類似岩石（製品）ｔ
        >   F395_431安山岩・同類似岩石（製品）ｔ
        >   F396_441大理石（製品）ｔ
        >   F397_451ぎょう灰岩（製品）ｔ
        >   F398_461砂岩（製品）ｔ
        >   F399_471粘板岩（製品）ｔ
        >   F400_491かんらん岩（粗鉱）ｔ
        >   F401_492かんらん岩（精鉱）ｔ
        >   F402_493オリビンサンド（製品）ｔ
        >   F403_511木節・頁岩粘土（粗鉱）ｔ
        >   F404_512木節・頁岩粘土（精鉱）ｔ
        >   F405_513がいろ目粘土（粗鉱）ｔ
        >   F406_514がいろ目粘土（精鉱）ｔ
        >   F407_521ろう石（粗鉱）ｔ
        >   F408_522ろう石（精鉱）ｔ
        >   F409_523ろう石クレー（製品）ｔ
        >   F410_531ドロマイト（粗鉱）ｔ
        >   F411_532ドロマイト（精鉱）ｔ
        >   F412_541長石（粗鉱）ｔ
        >   F413_542長石（精鉱）ｔ
        >   F414_543半花こう岩（粗鉱）ｔ
        >   F415_544半花こう岩（精鉱）ｔ
        >   F416_545風化花こう岩（含むサバ）（粗鉱）ｔ
        >   F417_546風化花こう岩（含むサバ）（精鉱）ｔ
        >   F418_551軟けい石（粗鉱）ｔ
        >   F419_552軟けい石（精鉱）ｔ
        >   F420_553白・炉材けい石（粗鉱）ｔ
        >   F421_554白・炉材けい石（精鉱）ｔ
        >   F422_561人造けい砂（製品）ｔ
        >   F423_562天然けい砂（含むがいろ目けい砂）（粗鉱）ｔ
        >   F424_563天然けい砂（含むがいろ目けい砂）（精鉱）ｔ
        >   F425_571石灰石（粗鉱）ｔ
        >   F426_572石灰石（精鉱）ｔ
        >   F427_591陶石（粗鉱）ｔ
        >   F428_592陶石（精鉱）ｔ
        >   F429_593陶石クレー（製品）ｔ
        >   F430_594カオリン（粗鉱）ｔ
        >   F431_595カオリン（精鉱）ｔ
        >   F432_911酸性白土（粗鉱）ｔ
        >   F433_912酸性白土（精鉱）ｔ
        >   F434_921ベントナイト（粗鉱）ｔ
        >   F435_922ベントナイト（精鉱）ｔ
        >   F436_931けいそう土（粗鉱）ｔ
        >   F437_932けいそう土（精鉱）ｔ
        >   F438_941滑石（粗鉱）ｔ
        >   F439_942滑石（精鉱）ｔ
    - K28,KMI,KMP 無視
    - KM28

        >    9111金鉱（精含量）ｇ
        >    9112銀鉱（精含量）ｋｇ
        >    9121鉛鉱（精含量）ｔ
        >    9122亜鉛鉱（精含量）ｔ
        >    9131鉄鉱（精含量）ｔ
        >    9191銅鉱（精含量）ｔ
        >    9199その他の金属鉱物【dummy】
        >    9211石炭（精炭）ｔ
        >    9221亜炭（精炭）ｔ
        >    9311原油ｋｌ
        >    9321天然ガス（基準状態）千?
        >    9329その他の原油・天然ガス【dummy】
        >    9411花こう岩・同類似岩石（製品）ｔ
        >    9421石英粗面岩・同類似岩石（製品）ｔ
        >    9431安山岩・同類似岩石（製品）ｔ
        >    9441大理石（製品）ｔ
        >    9451ぎょう灰岩（製品）ｔ
        >    9461砂岩（製品）ｔ
        >    9471粘板岩（製品）ｔ
        >    9481砂・砂利・玉石【dummy】
        >    9491かんらん岩（粗鉱）ｔ
        >    9492かんらん岩（精鉱）ｔ
        >    9493オリビンサンド（製品）ｔ
        >    9499その他の採石、砂・砂利・玉石【dummy】
        >    9511木節・頁岩粘土（粗鉱）ｔ
        >    9512木節・頁岩粘土（精鉱）ｔ
        >    9513がいろ目粘土（粗鉱）ｔ
        >    9514がいろ目粘土（精鉱）ｔ
        >    9519その他の耐火粘土【dummy】
        >    9521ろう石（粗鉱）ｔ
        >    9522ろう石（精鉱）ｔ
        >    9523ろう石クレー（製品）ｔ
        >    9531ドロマイト（粗鉱）ｔ
        >    9532ドロマイト（精鉱）ｔ
        >    9541長石（粗鉱）ｔ
        >    9542長石（精鉱）ｔ
        >    9543半花こう岩（粗鉱）ｔ
        >    9544半花こう岩（精鉱）ｔ
        >    9545風化花こう岩（含むサバ）（粗鉱）ｔ
        >    9546風化花こう岩（含むサバ）（精鉱）ｔ
        >    9551軟けい石（粗鉱）ｔ
        >    9552軟けい石（精鉱）ｔ
        >    9553白・炉材けい石（粗鉱）ｔ
        >    9554白・炉材けい石（精鉱）ｔ
        >    9561人造けい砂（製品）ｔ
        >    9562天然けい砂（含むがいろ目けい砂）（粗鉱）ｔ
        >    9563天然けい砂（含むがいろ目けい砂）（精鉱）ｔ
        >    9571石灰石（粗鉱）ｔ
        >    9572石灰石（精鉱）ｔ
        >    9591陶石（粗鉱）ｔ
        >    9592陶石（精鉱）ｔ
        >    9593陶石クレー（製品）ｔ
        >    9594カオリン（粗鉱）ｔ
        >    9595カオリン（精鉱）ｔ
        >    9599その他の窯業原料用鉱物【dummy】
        >    9911酸性白土（粗鉱）ｔ
        >    9912酸性白土（精鉱）ｔ
        >    9921ベントナイト（粗鉱）ｔ
        >    9922ベントナイト（精鉱）ｔ
        >    9931けいそう土（粗鉱）ｔ
        >    9932けいそう土（精鉱）ｔ
        >    9941滑石（粗鉱）ｔ
        >    9942滑石（精鉱）ｔ
        >    9999他に分類されないその他の鉱物【dummy】-}
{-# INLINE fデータ変換_生産_鉱業_数量 #-}
fデータ変換_生産_鉱業_数量 :: FileType -> HeaderTexts -> [Text] -> ValCars
fデータ変換_生産_鉱業_数量 ft hds tx
    | ft == K24  = k24
    | ft == KM28 = k28
    | otherwise  = Null

    where
        -- 取得する列のヘッダー
        wk24 = s24鉱業数量
        wk28 = s28鉱業数量

        -- ヘッダーからインデックスを取り,値と分類番号を取得
        k24Values = getValues           wk24 hds tx
        k28Values = getValues           wk28 hds tx
        k24Names  = translateGoodsCodes wk24 sd鉱業数量24
        k28Names  = translateGoodsCodes wk28 sd鉱業数量28
        --
        k24 = textToValCars k24Values k24Names
        k28 = textToValCars k28Values k28Names

--  *** H生産_鉱業_金額
-- ----------------------------------------------------------------

{- |
    * k24

        > F440_111金鉱（精含量）
        > F441_112銀鉱（精含量）
        > F442_121鉛鉱（精含量）
        > F443_122亜鉛鉱（精含量）
        > F444_131鉄鉱（精含量）
        > F445_191銅鉱（精含量）
        > F446_199その他の金属鉱物
        > F447_211石炭（精炭）
        > F448_221亜炭（精炭）
        > F449_311原油
        > F450_321天然ガス（基準状態）
        > F451_329他の原油・天然ガス
        > F452_411花こう岩・同類似岩石（製品）
        > F453_421石英粗面岩・同類似岩石（製品）
        > F454_431安山岩・同類似岩石（製品）
        > F455_441大理石（製品）
        > F456_451ぎょう灰岩（製品）
        > F457_461砂岩（製品）
        > F458_471粘板岩（製品）
        > F459_481砂・砂利・玉石
        > F460_491かんらん岩（粗鉱）
        > F461_492かんらん岩（精鉱）
        > F462_493オリビンサンド（製品）
        > F463_499その他の採石、砂・砂利・玉石
        > F464_511木節・頁岩粘土（粗鉱）
        > F465_512木節・頁岩粘土（精鉱）
        > F466_513がいろ目粘土（粗鉱）
        > F467_514がいろ目粘土（精鉱）
        > F468_519その他の耐火粘土
        > F469_521ろう石（粗鉱）
        > F470_522ろう石（精鉱）
        > F471_523ろう石クレー（製品）
        > F472_531ドロマイト（粗鉱）
        > F473_532ドロマイト（精鉱）
        > F474_541長石（粗鉱）
        > F475_542長石（精鉱）
        > F476_543半花こう岩（粗鉱）
        > F477_544半花こう岩（精鉱）
        > F478_545風化花こう岩（含むサバ）（粗鉱）
        > F479_546風化花こう岩（含むサバ）（精鉱）
        > F480_551軟けい石（粗鉱）
        > F481_552軟けい石（精鉱）
        > F482_553白・炉材けい石（粗鉱）
        > F483_554白・炉材けい石（精鉱）
        > F484_561人造けい砂（製品）
        > F485_562天然けい砂（含むがいろ目けい砂）（粗鉱）
        > F486_563天然けい砂（含むがいろ目けい砂）（精鉱）
        > F487_571石灰石（粗鉱）
        > F488_572石灰石（精鉱）
        > F489_591陶石（粗鉱）
        > F490_592陶石（精鉱）
        > F491_593陶石クレー（製品）
        > F492_594カオリン（粗鉱）
        > F493_595カオリン（精鉱）
        > F494_599その他の窯業原料用鉱物
        > F495_911酸性白土（粗鉱）
        > F496_912酸性白土（精鉱）
        > F497_921ベントナイト（粗鉱）
        > F498_922ベントナイト（精鉱）
        > F499_931けいそう土（粗鉱）
        > F500_932けいそう土（精鉱）
        > F501_941滑石（粗鉱）
        > F502_942滑石（精鉱）
        > F503_999他に分類されないその他の鉱物
    * KM28

        > 補正＿９１１１金鉱（精含量）
        > 補正＿９１１２銀鉱（精含量）
        > 補正＿９１２１鉛鉱（精含量）
        > 補正＿９１２２亜鉛鉱（精含量）
        > 補正＿９１３１鉄鉱（精含量）
        > 補正＿９１９１銅鉱（精含量）
        > 補正＿９１９９その他の金属鉱物
        > 補正＿９２１１石炭（精炭）
        > 補正＿９２２１亜炭（精炭）
        > 補正＿９３１１原油
        > 補正＿９３２１天然ガス（基準状態）
        > 補正＿９３２９その他の原油・天然ガス
        > 補正＿９４１１花こう岩・同類似岩石（製品）
        > 補正＿９４２１石英粗面岩・同類似岩石（製品）
        > 補正＿９４３１安山岩・同類似岩石（製品）
        > 補正＿９４４１大理石（製品）
        > 補正＿９４５１ぎょう灰岩（製品）
        > 補正＿９４６１砂岩（製品）
        > 補正＿９４７１粘板岩（製品）
        > 補正＿９４８１砂・砂利・玉石
        > 補正＿９４９１かんらん岩（粗鉱）
        > 補正＿９４９２かんらん岩（精鉱）
        > 補正＿９４９３オリビンサンド（製品）
        > 補正＿９４９９その他の採石、砂・砂利・玉石
        > 補正＿９５１１木節・頁岩粘土（粗鉱）
        > 補正＿９５１２木節・頁岩粘土（精鉱）
        > 補正＿９５１３がいろ目粘土（粗鉱）
        > 補正＿９５１４がいろ目粘土（精鉱）
        > 補正＿９５１９その他の耐火粘土
        > 補正＿９５２１ろう石（粗鉱）
        > 補正＿９５２２ろう石（精鉱）
        > 補正＿９５２３ろう石クレー（製品）
        > 補正＿９５３１ドロマイト（粗鉱）
        > 補正＿９５３２ドロマイト（精鉱）
        > 補正＿９５４１長石（粗鉱）
        > 補正＿９５４２長石（精鉱）
        > 補正＿９５４３半花こう岩（粗鉱）
        > 補正＿９５４４半花こう岩（精鉱）
        > 補正＿９５４５風化花こう岩（含むサバ）（粗鉱）
        > 補正＿９５４６風化花こう岩（含むサバ）（精鉱）
        > 補正＿９５５１軟けい石（粗鉱）
        > 補正＿９５５２軟けい石（精鉱）
        > 補正＿９５５３白・炉材けい石（粗鉱）
        > 補正＿９５５４白・炉材けい石（精鉱）
        > 補正＿９５６１人造けい砂（製品）
        > 補正＿９５６２天然けい砂（含むがいろ目けい砂）（粗鉱）
        > 補正＿９５６３天然けい砂（含むがいろ目けい砂）（精鉱）
        > 補正＿９５７１石灰石（粗鉱）
        > 補正＿９５７２石灰石（精鉱）
        > 補正＿９５９１陶石（粗鉱）
        > 補正＿９５９２陶石（精鉱）
        > 補正＿９５９３陶石クレー（製品）
        > 補正＿９５９４カオリン（粗鉱）
        > 補正＿９５９５カオリン（精鉱）
        > 補正＿９５９９その他の窯業原料用鉱物
        > 補正＿９９１１酸性白土（粗鉱）
        > 補正＿９９１２酸性白土（精鉱）
        > 補正＿９９２１ベントナイト（粗鉱）
        > 補正＿９９２２ベントナイト（精鉱）
        > 補正＿９９３１けいそう土（粗鉱）
        > 補正＿９９３２けいそう土（精鉱）
        > 補正＿９９４１滑石（粗鉱）
        > 補正＿９９４２滑石（精鉱）
        > 補正＿９９９９他に分類されないその他の鉱物-}
{-# INLINE fデータ変換_生産_鉱業_金額 #-}
fデータ変換_生産_鉱業_金額 :: FileType -> HeaderTexts -> [Text] -> ValCars
fデータ変換_生産_鉱業_金額 ft hds tx
    | ft == K24  = k24
    | ft == KM28 = k28
    | otherwise  = Null

    where
        -- 取得する列のヘッダー
        wk24 = s24鉱業金額
        wk28 = s28鉱業金額

        -- ヘッダーからインデックスを取り,値と分類番号を取得
        k24Values = getValues            wk24 hds tx
        k28Values = getValues            wk28 hds tx
        k24Names  = translateGoodsCodes  wk24 sd鉱業金額24
        k28Names  = translateGoodsCodes  wk28 sd鉱業金額28
        --
        k24 = textToValCars k24Values k24Names
        k28 = textToValCars k28Values k28Names


--  *** H生産_農林水産業_金額
-- ----------------------------------------------------------------

{- |
    * SC24

        >    01稲作
        >    02麦類・雑穀・豆類
        >    03いも類
        >    04工芸農作物
        >    05野菜（きのこ栽培を含む）
        >    06果樹類
        >    07花き・花木
        >    08その他の作物
        >    09酪農
        >    10肉用牛
        >    11養豚
        >    12養鶏
        >    13養蚕
        >    14その他の畜産
        >    15実験用・愛がん動物等
        >    16穀作作業
        >    17野菜・果樹作作業
        >    18その他の耕種作業
        >    19畜産
        >    20造園・植木業
        >    21育林業
        >    22素材生産業
        >    23育林サービス
        >    24素材生産サービス
        >    25山林種苗生産サービス
        >    26その他の林業サービス
        >    27薪炭生産
        >    28きのこ採取・うるし採取等
        >    29その他の林業（狩猟業等）
        >    30底びき網
        >    31地びき網・船びき網
        >    32まき網
        >    33刺網
        >    34定置網
        >    35釣・はえ縄
        >    36捕鯨
        >    37採貝・採藻
        >    38その他の海面漁業
        >    39内水面漁業
        >    40魚類養殖
        >    41貝類養殖
        >    42海藻類養殖
        >    43真珠養殖（真珠母貝養殖を除く）
        >    44種苗養殖（真珠母貝養殖を含む）
        >    45その他の海面養殖
        >    46内水面養殖業
    * SC28

        >    補正＿０１稲作
        >    補正＿０２麦類・雑穀・豆類
        >    補正＿０３いも類
        >    補正＿０４工芸農作物
        >    補正＿０５野菜（きのこ栽培を含む）
        >    補正＿０６果樹類
        >    補正＿０７花き・花木
        >    補正＿０８その他の作物
        >    補正＿０９酪農
        >    補正＿１０肉用牛
        >    補正＿１１養豚
        >    補正＿１２養鶏
        >    補正＿１３養蚕
        >    補正＿１４その他の畜産
        >    補正＿１５実験用・愛がん動物等
        >    補正＿１６穀作作業
        >    補正＿１７野菜・果樹作作業
        >    補正＿１８その他の耕種作業
        >    補正＿１９畜産
        >    補正＿２０造園・植木業
        >    補正＿２１育林業
        >    補正＿２２素材生産業
        >    補正＿２３育林サービス
        >    補正＿２４素材生産サービス
        >    補正＿２５山林種苗生産サービス
        >    補正＿２６その他の林業サービス
        >    補正＿２７薪炭生産
        >    補正＿２８きのこ採取・うるし採取等
        >    補正＿２９その他の林業（狩猟業等）
        >    補正＿３０底びき網
        >    補正＿３１地びき網・船びき網
        >    補正＿３２まき網
        >    補正＿３３刺網
        >    補正＿３４定置網
        >    補正＿３５釣・はえ縄
        >    補正＿３６捕鯨
        >    補正＿３７採貝・採藻
        >    補正＿３８その他の海面漁業
        >    補正＿３９内水面漁業
        >    補正＿４０魚類養殖
        >    補正＿４１貝類養殖
        >    補正＿４２海藻類養殖
        >    補正＿４３真珠養殖（真珠母貝養殖を除く）
        >    補正＿４４種苗養殖（真珠母貝養殖を含む）
        >    補正＿４５その他の海面養殖
        >    補正＿４６内水面養殖業
    * K無視-}
{-# INLINE fデータ変換_生産_農林漁業_金額 #-}
fデータ変換_生産_農林漁業_金額 :: FileType -> HeaderTexts -> [Text] -> Val
fデータ変換_生産_農林漁業_金額 ft hds tx
    | getFileYear ft == 24 && getFileDep ft == S && getFileInd ft == E農林漁業 = s24
    | getFileYear ft == 28 && getFileDep ft == S && getFileInd ft == E農林漁業 = s28
    | otherwise                                                                = Null

    where
        -- 取得する列のヘッダー
        ws24 = s24農林漁業金額
        ws28 = s28農林漁業金額

        -- ヘッダーからインデックスを取り,値と分類番号を取得
        s24Values = getValues          ws24 hds tx
        s28Values = getValues          ws28 hds tx
        s24Names  = translateGoodsCodes  ws24 sd農林漁業金額24
        s28Names  = translateGoodsCodes  ws28 sd農林漁業金額28
        --
        s24 = textToValCars s24Values s24Names
        s28 = textToValCars s28Values s28Names

--  *** H商品別卸売額
-- ----------------------------------------------------------------

{- |
    * 卸部門か小売部門か判別する.
    * k24  F954_卸売部門又は小売部門の別
    * KC28 卸売部門又は小売部門の別
    * S無視
    * K24

        > F955_[商業]分類番号１位
        > F956_[商業]分類番号２位
        > F957_[商業]分類番号３位
        > F958_[商業]分類番号４位
        > F959_[商業]分類番号５位
        > F960_[商業]分類番号６位
        > F961_[商業]分類番号７位
        > F962_[商業]分類番号８位
        > F963_[商業]分類番号９位
        > F964_[商業]分類番号10位
        > F965_[商業]販売金額１位
        > F966_[商業]販売金額２位
        > F967_[商業]販売金額３位
        > F968_[商業]販売金額４位
        > F969_[商業]販売金額５位
        > F970_[商業]販売金額６位
        > F971_[商業]販売金額７位
        > F972_[商業]販売金額８位
        > F973_[商業]販売金額９位
        > F974_[商業]販売金額10位
    * KC28

        > (商業)分類番号１位
        > (商業)分類番号２位
        > (商業)分類番号３位
        > (商業)分類番号４位
        > (商業)分類番号５位
        > (商業)分類番号６位
        > (商業)分類番号７位
        > (商業)分類番号８位
        > (商業)分類番号９位
        > (商業)分類番号10位
        > 補正＿［商業］販売金額１位
        > 補正＿［商業］販売金額２位
        > 補正＿［商業］販売金額３位
        > 補正＿［商業］販売金額４位
        > 補正＿［商業］販売金額５位
        > 補正＿［商業］販売金額６位
        > 補正＿［商業］販売金額７位
        > 補正＿［商業］販売金額８位
        > 補正＿［商業］販売金額９位
        > 補正＿［商業］販売金額１０位
    * K他 無視-}
{-# INLINE fデータ変換_商品別卸売額 #-}
fデータ変換_商品別卸売額 :: FileType -> HeaderTexts -> [Text] -> Val
fデータ変換_商品別卸売額 ft hds tx
    | getFileYear ft == 24 && getFileDep ft == K                           = k24
    | getFileYear ft == 28 && getFileDep ft == K && getFileInd ft == E商業 = k28
    | otherwise                                                            = Null

    where
        -- | 取得する列のヘッダー
        wk24' = T.pack "F954_卸売部門又は小売部門の別"   -- 表示形式確認せなできん
        wk28' = T.pack "卸売部門又は小売部門の別"        -- 表示形式確認
        wkc24  = s24商業分類
        wkv24  = s24商業金額
        wkc28  = s28商業分類
        wkv28  = s28商業金額

        -- | ヘッダーからインデックスを取り,値と分類番号を取得
        wk24Text = projFrom wk24' hds tx
        wk28Text = projFrom wk28' hds tx
        k24Values       = getValues       wkv24 hds tx
        k24TextValues   = getTextValues   wkc24 hds tx
        k28Values       = getValues       wkv28 hds tx
        k28TextValues   = getTextValues   wkc28 hds tx

        -- | 小売か卸売か判断
        isWholesale :: Text -> Bool
        isWholesale tx | T.pack "1" == tx       = True
                       | T.pack "2" == tx       = False
                       | T.null tx              = False
                       | T.pack " " == tx       = False
                       | tx  == T.pack "  "     = False
                       | otherwise              = error $ "fデータ変換_商品別卸売額 isWholesale 予期しない文字列: " ++ ushow tx

        -- | 小売ならNull
        f :: Bool -> Val -> Val
        f True  v = v
        f False v = Null
        --
        k24 = f (isWholesale wk24Text)
            $ textToValCars k24Values k24TextValues

        k28 = f (isWholesale wk28Text)
            $ textToValCars k28Values k28TextValues

--  *** H商品別小売額
-- ----------------------------------------------------------------
{-# INLINE fデータ変換_商品別小売額 #-}
fデータ変換_商品別小売額 :: FileType -> HeaderTexts -> [Text] -> Val
fデータ変換_商品別小売額 ft hds tx
    | getFileYear ft == 24 && getFileDep ft == K                           = s24
    | getFileYear ft == 28 && getFileDep ft == K && getFileInd ft == E商業 = s28
    | otherwise                                                            = Null

    where
        -- 取得する列のヘッダー
        wk24' = T.pack "F954_卸売部門又は小売部門の別"
        wk28' = T.pack "卸売部門又は小売部門の別"
        wkc24  = s24商業分類
        wkv24  = s24商業金額
        wkc28  = s28商業分類
        wkv28  = s28商業金額

        -- | ヘッダーからインデックスを取り,値と分類番号を取得
        -- 小売か卸売か判断
        isRetail :: Text -> Bool
        isRetail tx | T.pack "2" == tx      = True
                    | T.pack "1" == tx      = False
                    | T.null tx             = False
                    | T.pack " " == tx      = False
                    | tx  == T.pack "  "    = False
                    | otherwise             = error $ "fデータ変換_商品別小売額 isRetail 予期しない文字列" ++ ushow tx

        -- 小売ならNull
        f :: Bool -> Val -> Val
        f True  v = v
        f False v = Null


        wk24Text        = projFrom wk24' hds tx
        wk28Text        = projFrom wk24' hds tx
        k24Values       = getValues       wkv24 hds tx
        k28Values       = getValues       wkv28 hds tx
        k24TextValues   = getTextValues   wkc24 hds tx
        k28TextValues   = getTextValues   wkc28 hds tx

        --
        s24 = f (isRetail wk24Text)
            $textToValCars k24Values k24TextValues

        s28 = f (isRetail wk28Text)
            $ textToValCars k28Values k28TextValues

--  *** H事業所形態_医療福祉
-- ----------------------------------------------------------------
{-# INLINE fデータ変換_事業所形態_医療福祉 #-}
fデータ変換_事業所形態_医療福祉 :: FileType -> HeaderTexts -> [Text] -> Val
fデータ変換_事業所形態_医療福祉 ft hds tx
    | getFileYear ft == 24 && getFileInd ft == E医療福祉 = s24
    | getFileYear ft == 28 && getFileInd ft == E医療福祉 = s28
    | otherwise                                          = Null
    where
        -- | 取得する列のヘッダー
        ws24  = T.pack "事業所の形態、主な事業の内容"
        ws28  = T.pack "事業所の形態、主な事業の内容"
        -- | ヘッダーからインデックスを取り,値を取得

        s24text = projFrom ws24 hds tx
        s28text = projFrom ws28 hds tx
        -- | 4桁の場合先頭に0を足す
        --    全体的に01と1の書き方が混在している
        f :: Text -> Val
        f tx    | tx  == T.pack "01"  = g E一般病院
                | tx  == T.pack "02"  = g E精神科病院
                | tx  == T.pack "03"  = g E有床診療所
                | tx  == T.pack "04"  = g E無床診療所
                | tx  == T.pack "05"  = g E歯科診療所
                | tx  == T.pack "06"  = g E助産所助産師業
                | tx  == T.pack "07"  = g E看護業
                | tx  == T.pack "08"  = g E施術業
                | tx  == T.pack "09"  = g Eその他の療養所
                | tx  == T.pack "10"  = g E歯科技工所
                | tx  == T.pack "11"  = g Eその他の医療に附帯するサービス業
                | tx  == T.pack "12"  = g E結核健康相談施設
                | tx  == T.pack "13"  = g E精神保健相談施設
                | tx  == T.pack "14"  = g E母子健康相談施設
                | tx  == T.pack "15"  = g Eその他の健康相談施設
                | tx  == T.pack "16"  = g E検査業
                | tx  == T.pack "17"  = g E消毒業
                | tx  == T.pack "18"  = g Eその他の保健衛生
                | tx  == T.pack "19"  = g E社会保険事業団体
                | tx  == T.pack "20"  = g E保育所
                | tx  == T.pack "21"  = g Eその他の児童福祉事業
                | tx  == T.pack "22"  = g E特別養護老人ホーム
                | tx  == T.pack "23"  = g E介護老人保健施設
                | tx  == T.pack "24"  = g E通所短期入所介護事業
                | tx  == T.pack "25"  = g E訪問介護事業
                | tx  == T.pack "26"  = g E認知症老人グループホーム
                | tx  == T.pack "27"  = g E有料老人ホーム
                | tx  == T.pack "28"  = g Eその他の老人福祉介護事業
                | tx  == T.pack "29"  = g E居住支援事業
                | tx  == T.pack "30"  = g Eその他の障碍者福祉事業
                | tx  == T.pack "31"  = g E更生保護事業
                | tx  == T.pack "32"  = g Eその他の社会保険社会福祉介護事業
                | tx  == T.pack " "   = Null
                | tx  == T.pack "  "  = Null
                | T.null tx           = Null
                | otherwise           = error $ "予期しない文字列 fデータ変換_事業所形態_医療福:" ++ ushow tx
                where g = V事業所形態_医療福祉

        s24 = f s24text
        s28 = f s28text

--  *** H事業収入_医療福祉
-- ----------------------------------------------------------------
{-# INLINE fデータ変換_事業収入_医療福祉 #-}
fデータ変換_事業収入_医療福祉 :: FileType -> HeaderTexts -> [Text] -> Val
fデータ変換_事業収入_医療福祉 ft hds tx
    | getFileYear ft == 24 && getFileInd ft == E医療福祉 = s24
    | getFileYear ft == 28 && getFileInd ft == E医療福祉 = s28
    | otherwise                                          = Null

    where
        -- 取得する列のヘッダー
        ws24 = s24医療福祉
        ws28 = s28医療福祉

        -- ヘッダーからインデックスを取り,値と分類番号を取得
        s24Values = getValues ws24 hds tx
        s28Values = getValues ws28 hds tx

        f :: [Double] -> Val
        f xs | and (map (0==) xs) = Null
             | otherwise = V事業収入_医療福祉 $ E事業収入_医療福祉
                            { _保険診療収入         = xs !! 0
                            , _保険外診療収入       = xs !! 1
                            , _施設介護収入         = xs !! 2
                            , _通所介護訪問介護収入 = xs !! 3
                            , _社会保険事業収入     = xs !! 4
                            , _保健衛生事業収入     = xs !! 5
                            , _社会福祉事業収入     = xs !! 6 }

        --
        s24 =  f s24Values
        s28 =  f s28Values

--  *** H出荷額_製造業(24年)
-- ----------------------------------------------------------------

-- | ｢出荷額,在庫額,加工賃,製造業以外｣はKMP のみデータの構造が他と異なるため,別の処理を行う必要がある.
-- Cars を返す
{-# INLINE fデータ変換_出荷額_製造業#-}
fデータ変換_出荷額_製造業 :: FileType -> HeaderTexts -> [Text] -> ValCars
fデータ変換_出荷額_製造業 ft hds tx
    | ft == K24   = k24
    | otherwise   = Null

    where
        -- 取得する列のヘッダー
        wkc24   = s24製造業出荷分類
        wkv24   = s24製造業出荷金額

        -- ヘッダーからインデックスを取り,値と分類番号を取得
        k24Values       = getValues       wkv24 hds tx
        k24TextValues   = getTextValues   wkc24 hds tx
        --
        k24 = textToValCars k24Values k24TextValues

--  *** H在庫額_製造業
--- ---------------------------------------------------------------

-- | 出荷額,在庫額,加工賃,製造業以外KMP のみデータの構造が他と異なるため,別の処理を行う必要がある.
-- * K24
{-# INLINE fデータ変換_在庫額_製造業 #-}
fデータ変換_在庫額_製造業 :: FileType -> HeaderTexts -> [Text] -> ValCars
fデータ変換_在庫額_製造業 ft hds tx
    | ft == K24   = k24
    | otherwise   = Null

    where
        -- 取得する列のヘッダー
        wkc24   = s24製造業出荷分類
        wkv24   = s24製造業在庫金額

        -- ヘッダーからインデックスを取り,値と分類番号を取得
        k24Values       = getValues       wkv24 hds tx
        k24TextValues   = getTextValues   wkc24 hds tx

        --
        k24 = textToValCars k24Values k24TextValues

--  *** H収入額_加工賃
------------------------------------------------------------------

-- | 出荷額,在庫額,加工賃,製造業以外KMP のみデータの構造が他と異なるため,別の処理を行う必要がある.
-- * K24
{-# INLINE fデータ変換_収入額_加工賃 #-}
fデータ変換_収入額_加工賃 :: FileType -> HeaderTexts -> [Text] -> ValCars
fデータ変換_収入額_加工賃 ft hds tx
    | ft == K24   = k24
    | otherwise   = Null

    where
        -- 取得する列のヘッダー
        wkc24   = s24製造業加工賃分類
        wkv24   = s24製造業加工賃金額

        -- ヘッダーからインデックスを取り,値と分類番号を取得
        k24Values       = getValues       wkv24 hds tx
        k24TextValues   = getTextValues   wkc24 hds tx
        --
        k24 = textToValCars k24Values k24TextValues


--   H収入額_製造業以外
------------------------------------------------------------------
-- |* K24    : VDC.s24製造業製造業以外
--  28 年は KMPなので独自に変換
{-# INLINE fデータ変換_収入額_製造業以外 #-}
fデータ変換_収入額_製造業以外 :: FileType -> HeaderTexts -> [Text] -> ValCars
fデータ変換_収入額_製造業以外 ft hds tx
    | ft == K24   = k24
    | otherwise   = Null

    where
        -- 取得する列のヘッダー
        wk24   = s24製造業製造業以外
        -- ヘッダーからインデックスを取り,値と分類番号を取得

        k24Values       = getValues wk24 hds tx
        k24Names        = translateGoodsCodes  wk24 sd収入額_製造業以外24
        k24             = textToValCars k24Values k24Names



-- *** H原材料使用額
------------------------------------------------------------------

{- |
非製造業からの委託を受けて生産する 分については、
次に掲げる式により、加工賃収入 額に付加価値率の逆数を乗ずることにより、原材 料費等を含んだ国内生産額を推計している。
(IO推計解説書 pp35)

[\国内生産額 = 加工賃収入額 \times \frac{製品価額}{製品額-原材料費}\]


K24 : F508_原材料使用額
KMI28 : 原材料使用額

-}
{-# INLINE fデータ変換_原材料使用額  #-}
fデータ変換_原材料使用額 :: FileType -> HeaderTexts -> [Text] -> ValDouble
fデータ変換_原材料使用額 ft hds tx
    | ft == K24   = k24
    | ft == KMI28 = kmi28
    | otherwise   = Null

    where
        -- 取得する列のヘッダー
        wk24   = T.pack "F508_原材料使用額"
        wkmi28 = T.pack "原材料使用額"

        k24       = textToValDouble $! projFrom wk24   hds tx
        kmi28     = textToValDouble $! projFrom wkmi28 hds tx


--  *** H収入内訳_学校
------------------------------------------------------------------
{-# INLINE  fデータ変換_収入内訳_学校 #-}
fデータ変換_収入内訳_学校 :: FileType -> HeaderTexts -> [Text] -> ValCars
fデータ変換_収入内訳_学校 ft hds tx
    | ft == SJ24  = s24
    | ft == SJ28  = s28
    | otherwise   = Null

    where
        -- 取得する列のヘッダー
        ws24   = s24学校教育
        ws28   = s28学校教育
        -- ヘッダーからインデックスを取り,値と分類番号を取得
        s24Values = getValues ws24 hds tx
        s28Values = getValues ws28 hds tx
        s24Names  = translateGoodsCodes  ws24 sd学校教育24
        s28Names  = translateGoodsCodes  ws28 sd学校教育28
        --
        s24 = textToValCars s24Values s24Names
        s28 = textToValCars s28Values s28Names


-- *** H学校等の種類
------------------------------------------------------------------

-- | SJ24 : 学校等の種類
--   SJ28 : 学校教育の種類
{-# INLINE fデータ変換_学校等の種類 #-}
fデータ変換_学校等の種類 :: FileType -> HeaderTexts -> [Text] -> ValText
fデータ変換_学校等の種類 ft hds tx
    | ft == SJ24 = sj24
    | ft == SJ28 = sj28
    | otherwise  = Null
    where
        -- 取得する列のヘッダー
        wsj24 = T.pack "学校等の種類"
        wsj28 = T.pack "学校教育の種類"

        sj24Text  = textToDigitText $! projFrom wsj24 hds tx
        sj28Text  = textToDigitText $! projFrom wsj28 hds tx

        f tx | T.null tx            = Null
             | tx  == T.pack " "    = Null
             | tx  == T.pack "  "   = Null
             | otherwise            = VText tx

        sj24 = f sj24Text
        sj28 = f sj28Text


-- *** H年初製造品在庫額
------------------------------------------------------------------

-- |
-- * K24   :F536_[年初]製造品①
-- * KMI28 : 年初在庫製造品
{-# INLINE fデータ変換_年初製造品在庫額#-}
fデータ変換_年初製造品在庫額 :: FileType -> HeaderTexts -> [Text] -> Val
fデータ変換_年初製造品在庫額 ft hds tx
    | ft == K24   = k24
    | ft == KMI28 = k28
    | otherwise   = Null
    where
        -- 取得する列のヘッダー
        wk24 = T.pack "F536_[年初]製造品①"
        wk28 = T.pack "年初在庫製造品"
        -- ヘッダーからインデックスを取り,値を取得

        k24text = projFrom wk24 hds tx
        k28text = projFrom wk28 hds tx
        --

        k24 = textToValDouble k24text
        k28 = textToValDouble k28text

-- *** H年末製造品在庫額
------------------------------------------------------------------

-- |
-- * K24   : F537_[年末]製造品①
-- * KMI28 : 年末在庫製造品
{-# INLINE fデータ変換_年末製造品在庫額 #-}
fデータ変換_年末製造品在庫額 :: FileType -> HeaderTexts -> [Text] -> Val
fデータ変換_年末製造品在庫額 ft hds tx
    | ft == K24   = k24
    | ft == KMI28 = k28
    | otherwise   = Null
    where
        -- 取得する列のヘッダー
        wk24 = T.pack "F537_[年末]製造品①"
        wk28 = T.pack "年末在庫製造品"
        -- ヘッダーからインデックスを取り,値を取得

        k24text = projFrom wk24 hds tx
        k28text = projFrom wk28 hds tx
        --
        k24 = textToValDouble k24text
        k28 = textToValDouble k28text

-- *** H年初半製品及び仕掛品
------------------------------------------------------------------

-- |
-- * K24   : F538_F538_[年初]半製品及び仕掛品②
-- * KMI28 : 年初在庫半製品
{-# INLINE fデータ変換_年初半製品及び仕掛品 #-}
fデータ変換_年初半製品及び仕掛品 :: FileType -> HeaderTexts -> [Text] -> Val
fデータ変換_年初半製品及び仕掛品 ft hds tx
    | ft == K24   = k24
    | ft == KMI28 = k28
    | otherwise   = Null
    where
        -- 取得する列のヘッダー
        wk24 = T.pack "F538_[年初]半製品及び仕掛品②"
        wk28 = T.pack "年初在庫半製品"
        -- ヘッダーからインデックスを取り,値を取得

        k24text = projFrom wk24 hds tx
        k28text = projFrom wk28 hds tx
        --

        k24 = textToValDouble k24text
        k28 = textToValDouble k28text


-- *** H年末半製品及び仕掛品
------------------------------------------------------------------

-- |
-- * K24   : F539_[年末]半製品及び仕掛品②
-- * KMI28 : 年末在庫半製品
{-# INLINE fデータ変換_年末半製品及び仕掛品 #-}
fデータ変換_年末半製品及び仕掛品 :: FileType -> HeaderTexts -> [Text] -> Val
fデータ変換_年末半製品及び仕掛品 ft hds tx
    | ft == K24   = k24
    | ft == KMI28 = k28
    | otherwise   = Null
    where
        -- 取得する列のヘッダー
        wk24 = T.pack "F539_[年末]半製品及び仕掛品②"
        wk28 = T.pack "年末在庫半製品"
        -- ヘッダーからインデックスを取り,値を取得

        k24text = projFrom wk24 hds tx
        k28text = projFrom wk28 hds tx
        --

        k24 = textToValDouble k24text
        k28 = textToValDouble k28text

-- *** H年初原材料及び燃料
------------------------------------------------------------------

-- |
-- * K24   : F540_[年初]原材料及び燃料③
-- * KMI28 : 年初在庫原材料
{-# INLINE fデータ変換_年初原材料及び燃料#-}
fデータ変換_年初原材料及び燃料 :: FileType -> HeaderTexts -> [Text] -> Val
fデータ変換_年初原材料及び燃料 ft hds tx
    | ft == K24   = k24
    | ft == KMI28 = k28
    | otherwise   = Null
    where
        -- 取得する列のヘッダー
        wk24 = T.pack "F540_[年初]原材料及び燃料③"
        wk28 = T.pack "年初在庫原材料"
        -- ヘッダーからインデックスを取り,値を取得

        k24text = projFrom wk24 hds tx
        k28text = projFrom wk28 hds tx
        --

        k24 = textToValDouble k24text
        k28 = textToValDouble k28text

-- *** H年末原材料及び燃料
------------------------------------------------------------------

-- |
-- * K24   : F540_[年初]原材料及び燃料③
-- * KMI28 : 年末在庫原材料
{-# INLINE fデータ変換_年末原材料及び燃料#-}
fデータ変換_年末原材料及び燃料 :: FileType -> HeaderTexts -> [Text] -> Val
fデータ変換_年末原材料及び燃料 ft hds tx
    | ft == K24   = k24
    | ft == KMI28 = k28
    | otherwise   = Null
    where
        -- 取得する列のヘッダー
        wk24 = T.pack "F540_[年初]原材料及び燃料③"
        wk28 = T.pack "年末在庫原材料"
        -- ヘッダーからインデックスを取り,値を取得

        k24text = projFrom wk24 hds tx
        k28text = projFrom wk28 hds tx
        --

        k24 = textToValDouble k24text
        k28 = textToValDouble k28text

-- *** H商品別リース契約高
------------------------------------------------------------------

{- | Cars
    nameは産業細分類に変換
     * SM24

         > [リース]産業機械
         > [リース]工作機械
         > [リース]土木・建設機械
         > [リース]医療用機器
         > [リース]商業用機械・設備
         > [リース]通信機器
         > [リース]サービス業用機械・設備
         > [リース]その他の産業用機械・設備
         > [リース]電子計算機・同関連機器
         > [リース]事務用機器
         > [リース]自動車
         > [リース]スポーツ・娯楽用品
         > [リース]映画・演劇用品
         > [リース]音楽・映像記録物
         > [リース]貸衣しょう
         > [リース]その他
     * SM28

         > [リース]産業機械
         > [リース]工作機械
         > [リース]土木・建設機械
         > [リース]医療用機器
         > [リース]商業用機械・設備
         > [リース]通信機器
         > [リース]サービス業用機械・設備
         > [リース]その他の産業用機械・設備
         > [リース]電子計算機・同関連機器
         > [リース]事務用機器
         > [リース]自動車
         > [リース]スポーツ・娯楽用品
         > [リース]映画・演劇用品
         > [リース]音楽・映像記録物
         > [リース]貸衣しょう
         > [リース]その他 -}
{-# INLINE fデータ変換_商品別リース契約高 #-}
fデータ変換_商品別リース契約高  :: FileType -> HeaderTexts -> [Text] -> Val
fデータ変換_商品別リース契約高  ft hds tx
    | ft == SM24 = s24
    | ft == SM28 = s28
    | otherwise   = Null

    where
        -- 取得する列のヘッダー
        ws24   = s24商品別リース契約高
        ws28   = s28商品別リース契約高

        -- ヘッダーからインデックスを取り,値と分類番号を取得
        s24Values = getValues ws24 hds tx
        s24Names  = translateGoodsCodes s24商品別リース契約高 sd物品賃貸業リース

        s28Values = getValues ws28 hds tx
        s28Names  = translateGoodsCodes s28商品別リース契約高 sd物品賃貸業リース

        --
        s24 = VCars $! VDS.mergeSameNameCars $! textToCars s24Values s24Names

        s28 = VCars $! VDS.mergeSameNameCars $! textToCars s28Values s28Names

-- *** H商品別レンタル売上高
------------------------------------------------------------------

{- | Cars
      nameは産業細分類に変換
      * SM24

         > [レンタル]産業機械
         > [レンタル]工作機械
         > [レンタル]土木・建設機械
         > [レンタル]医療用機器
         > [レンタル]商業用機械・設備
         > [レンタル]通信機器
         > [レンタル]サービス業用機械・設備
         > [レンタル]その他の産業用機械・設備
         > [レンタル]電子計算機・同関連機器
         > [レンタル]事務用機器
         > [レンタル]自動車
         > [レンタル]スポーツ・娯楽用品
         > [レンタル]映画・演劇用品
         > [レンタル]音楽・映像記録物
         > [レンタル]貸衣しょう
         > [レンタル]その他
    * SM28

         > [レンタル]産業機械
         > [レンタル]工作機械
         > [レンタル]土木・建設機械
         > [レンタル]医療用機器
         > [レンタル]商業用機械・設備
         > [レンタル]通信機器
         > [レンタル]サービス業用機械・設備
         > [レンタル]その他の産業用機械・設備
         > [レンタル]電子計算機・同関連機器
         > [レンタル]事務用機器
         > [レンタル]自動車
         > [レンタル]スポーツ・娯楽用品
         > [レンタル]映画・演劇用品
         > [レンタル]音楽・映像記録物
         > [レンタル]貸衣しょう
         > [レンタル]その他 -}
{-# INLINE fデータ変換_商品別レンタル売上高 #-}
fデータ変換_商品別レンタル売上高 :: FileType -> HeaderTexts -> [Text] -> ValCars
fデータ変換_商品別レンタル売上高 ft hds tx
    | ft == SM24 = s24
    | ft == SM28 = s28
    | otherwise   = Null

    where
        -- 取得する列のヘッダー
        ws24   = s24商品別レンタル売上高
        ws28   = s28商品別レンタル売上高

        -- ヘッダーからインデックスを取り,値と分類番号を取得
        -- ここで事業番号に変換してしまう. より細かくする場合はここから変更する必要がある.
        s24Values = getValues ws24 hds tx
        s24Names  =  translateGoodsCodes s24商品別レンタル売上高 sd物品賃貸業レンタル

        s28Values = getValues ws28 hds tx
        s28Names  =  translateGoodsCodes s28商品別レンタル売上高 sd物品賃貸業レンタル

        --
        s24 = VCars $! VDS.mergeSameNameCars $! textToCars s24Values s24Names
        s28 = VCars $! VDS.mergeSameNameCars $! textToCars s28Values s28Names

-- *** Hレンタル総売上高
------------------------------------------------------------------

-- | VDouble
-- * SM24 : レンタル年間売上高
-- * SM28 : 補正＿レンタル年間売上高
{-# INLINE fデータ変換_レンタル総売上高 #-}
fデータ変換_レンタル総売上高 :: FileType -> HeaderTexts -> [Text] -> Val
fデータ変換_レンタル総売上高 ft hds tx
    | ft == SM24 = s24
    | ft == SM28 = s28
    | otherwise  = Null
    where
        -- 取得する列のヘッダー
        ws24 = T.pack "レンタル年間売上高"
        ws28 = T.pack "補正＿レンタル年間売上高"
        -- ヘッダーからインデックスを取り,値を取得

        s24text = projFrom ws24 hds tx
        s28text = projFrom ws28 hds tx
        --

        s24 = textToValDouble s24text
        s28 = textToValDouble s28text


-- *** Hリース年間契約高
------------------------------------------------------------------

-- | VDouble
-- * SM24 : リース年間契約高
-- * SM28 : 補正＿リース年間契約高
{-# INLINE fデータ変換_リース年間契約高 #-}
fデータ変換_リース年間契約高 :: FileType -> HeaderTexts -> [Text] -> Val
fデータ変換_リース年間契約高 ft hds tx
    | ft == SM24 = s24
    | ft == SM28 = s28
    | otherwise  = Null
    where
        -- 取得する列のヘッダー
        ws24 = T.pack "リース年間契約高"
        ws28 = T.pack "補正＿リース年間契約高"
        -- ヘッダーからインデックスを取り,値を取得

        s24text = projFrom ws24 hds tx
        s28text = projFrom ws28 hds tx
        --
        s24 = textToValDouble s24text
        s28 = textToValDouble s28text

-- *** HサービスB相手先収入割合
------------------------------------------------------------------

-- | VDouble
-- * S24 :

        -- > ㈰個人（一般消費者）
        -- > ㈪民間
        -- > ㈫公務（官公庁）
        -- > ㈬海外取引
        -- > ㈭同一企業内取引
-- * S28

        -- > [サＢ]㈰個人（一般消費者）
        -- > [サＢ]㈪民間
        -- > [サＢ]㈫公務（官公庁）
        -- > [サＢ]㈬海外取引
        -- > [サＢ]㈭同一企業内取引
{-# INLINE fデータ変換_相手先別収入割合_サB #-}
fデータ変換_相手先別収入割合_サB :: FileType -> HeaderTexts -> [Text] -> Val
fデータ変換_相手先別収入割合_サB ft hds tx
    | getFileYear ft == 24 && getFileInd ft == EサービスB = s24
    | getFileYear ft == 28 && getFileInd ft == EサービスB = s28
    | otherwise                                          = Null

    where
        -- 取得する列のヘッダー
        ws24 = s24相手先別収入割合_サB
        ws28 = s28相手先別収入割合_サB

        -- ヘッダーからインデックスを取り,値と分類番号を取得
        s24Values = getValues ws24 hds tx
        s28Values = getValues ws28 hds tx

        f :: [Double] -> Val
        f xs    | and (map (0 ==) xs) = Null
                | otherwise = V相手先別収入割合 $ E相手先別収入割合
                            { _一般消費者           = xs !! 0
                            , _民間企業             = xs !! 1
                            , _官公庁               = xs !! 2
                            , _海外取引             = xs !! 3
                            , _同一企業             = xs !! 4 }

        --
        s24 = f s24Values
        s28 = f s28Values

-- *** H相手先別収入割合_医療福祉
------------------------------------------------------------------

{- | V相手先別収入割合_医療福祉
        * S24   :

        > ①個人（一般消費者）
        > ②民間
        > ③公務（官公庁）
        > ④海外取引
        > ⑤同一企業内取引
    * S28   :

        > ㈰個人（一般消費者）
        > ㈪民間
        > ㈫公務（官公庁）
        > ㈬海外取引
        > ㈭同一企業内取引 -}
{-# INLINE fデータ変換_相手先別収入割合_医療福祉 #-}
fデータ変換_相手先別収入割合_医療福祉 :: FileType -> HeaderTexts -> [Text] -> Val
fデータ変換_相手先別収入割合_医療福祉 ft hds tx
    | getFileYear ft == 24 && getFileInd ft == E医療福祉 = s24
    | getFileYear ft == 28 && getFileInd ft == E医療福祉 = s28
    | otherwise                                          = Null

    where
        -- 取得する列のヘッダー
        ws24 = s24相手先別収入割合_医療福祉
        ws28 = s28相手先別収入割合_医療福祉

        -- ヘッダーからインデックスを取り,値と分類番号を取得
        s24Values = getValues ws24 hds tx
        s28Values = getValues ws28 hds tx

        f :: [Double] -> Val
        f xs    | and (map (0==) xs) = Null
                | otherwise =   V相手先別収入割合 $ E相手先別収入割合
                                { _一般消費者           = xs !! 0
                                , _民間企業             = xs !! 1
                                , _官公庁               = xs !! 2
                                , _海外取引             = xs !! 3
                                , _同一企業             = xs !! 4 }

        --
        s24 = f s24Values
        s28 = f s28Values

-- *** H修理手数料収入_商業
------------------------------------------------------------------


-- | VDouble
-- * K24  : F989_修理料収入額
-- * KC28 : 補正＿修理料収入額
-- * S    : 対応項目なし
{-# INLINE fデータ変換_修理手数料収入_商業 #-}
fデータ変換_修理手数料収入_商業 :: FileType -> HeaderTexts -> [Text] -> ValDouble
fデータ変換_修理手数料収入_商業 ft hds tx
    | ft == K24   = k24
    | ft == KC28  = k28
    | otherwise   = Null
    where
        -- 取得する列のヘッダー
        wk24 = T.pack "F989_修理料収入額"
        wk28 = T.pack "補正＿修理料収入額"
        -- ヘッダーからインデックスを取り,値を取得
        k24text = projFrom wk24 hds tx
        k28text = projFrom wk28 hds tx
        --
        k24 = textToValDouble k24text
        k28 = textToValDouble k28text

-- *** H仲立手数料収入_商業
------------------------------------------------------------------


-- | VDouble
-- * k24  F987_仲立手数料収入額
-- * KC28 補正＿仲立手数料収入額
{-# INLINE fデータ変換_仲立手数料収入_商業 #-}
fデータ変換_仲立手数料収入_商業 :: FileType -> HeaderTexts -> [Text] -> ValDouble
fデータ変換_仲立手数料収入_商業 ft hds tx
    | ft == K24   = k24
    | ft == KC28  = k28
    | otherwise   = Null
    where
        -- 取得する列のヘッダー
        wk24 = T.pack "F987_仲立手数料収入額"
        wk28 = T.pack "補正＿仲立手数料収入額"
        -- ヘッダーからインデックスを取り,値を取得
        k24text = projFrom wk24 hds tx
        k28text = projFrom wk28 hds tx
        --
        k24 = textToValDouble k24text
        k28 = textToValDouble k28text

-- *** H商品売上原価
-- ----------------------------------------------------------------

-- | VDouble
-- 24年のみ
{-# INLINE fデータ変換_商品売上原価 #-}
fデータ変換_商品売上原価 :: FileType -> HeaderTexts -> [Text] -> Val
fデータ変換_商品売上原価 ft hds tx
    | getFileYear ft == 24 && getFileDep ft == K = k24
    | getFileYear ft == 24 && getFileDep ft == S = s24
    | otherwise   = Null
    where
        -- 取得する列のヘッダー
        wk24 = T.pack "F1897_[企]商品売上原価"
        ws24 = T.pack "[企]商品売上原価"
        -- ヘッダーからインデックスを取り,値を取得
        k24text = projFrom wk24 hds tx
        s24text = projFrom ws24 hds tx
        --
        k24 = textToValDouble k24text
        s24 = textToValDouble s24text

-- *** H年初商品手持額
------------------------------------------------------------------

-- | VDouble
-- * KC28のみ
-- * KC28 : 補正＿年初商品手持額
{-# INLINE fデータ変換_年初商品手持額 #-}
fデータ変換_年初商品手持額 :: FileType -> HeaderTexts -> [Text] -> Val
fデータ変換_年初商品手持額 ft hds tx
    | ft == KC28    = kc28
    | otherwise     = Null
    where
        -- 取得する列のヘッダー
        wkc28  = T.pack "補正＿年初商品手持額"
        -- ヘッダーからインデックスを取り,値を取得
        kc28text   = projFrom wkc28 hds tx
        --
        kc28  = textToValDouble kc28text


-- *** H年末商品手持額
------------------------------------------------------------------

-- | 28年Kのみ
-- * KC28 : 補正＿年末商品手持額
{-# INLINE fデータ変換_年末商品手持額 #-}
fデータ変換_年末商品手持額 :: FileType -> HeaderTexts -> [Text] -> ValDouble
fデータ変換_年末商品手持額 ft hds tx
    | ft == KC28    = kc28
    | otherwise     = Null
    where
        -- 取得する列のヘッダー
        wkc28  = T.pack "補正＿年末商品手持額"
        -- ヘッダーからインデックスを取り,値を取得
        kc28text   = projFrom wkc28 hds tx
        --
        kc28  = textToValDouble kc28text

-- *** H年間仕入額
------------------------------------------------------------------

-- |
-- * KMI28 : 転売した商品の仕入額
-- * KC28  : 補正＿年間商品仕入額
-- * K24   : F513_転売した商品の仕入額
-- * S     : 該当項目なし
{-# INLINE fデータ変換_年間仕入額 #-}
fデータ変換_年間仕入額 :: FileType -> HeaderTexts -> [Text] -> Val
fデータ変換_年間仕入額 ft hds tx
    | ft == KMI28   = kmi28
    | ft == KC28    = kc28
    | ft == K24     = k24
    | otherwise     = Null
    where
        -- 取得する列のヘッダー
        wk24   = T.pack "F513_転売した商品の仕入額"
        wkc28  = T.pack "補正＿年間商品仕入額"
        wkmi28 = T.pack "転売した商品の仕入額"

        -- ヘッダーからインデックスを取り,値を取得
        k24text    = projFrom wk24    hds tx
        kc28text   = projFrom wkc28   hds tx
        kmi28text  = projFrom wkmi28  hds tx
        --
        k24   = textToValDouble k24text
        kc28  = textToValDouble kc28text
        kmi28 = textToValDouble kmi28text

------------------------------------------------------------------

--  | H対象年度
{-# INLINE fデータ変換_対象年度 #-}
fデータ変換_対象年度 :: FileType -> HeaderTexts -> [Text] -> Val
fデータ変換_対象年度 ft hds tx
    | getFileYear ft == 24 = VInt 24
    | getFileYear ft == 28 = VInt 28
    | otherwise            = Null


-- *** H消費税記入の別
------------------------------------------------------------------

{- |
    * s24 "消費税の取扱い　" 全角スペースが混ざっているので注意（素敵ですね）


         > 1 消費税抜き △ 消費税込


    * k24 F137_消費税の取扱い

        > 1 消費税抜き △ 消費税込 -- 要確認
    * 28 デフォルトで税込み  -}
{-# INLINE fデータ変換_消費税記入の別 #-}
fデータ変換_消費税記入の別 :: FileType -> HeaderTexts -> [Text] -> Val
fデータ変換_消費税記入の別 ft hds tx
    | getFileYear ft == 24 && getFileDep ft == S = s24
    | getFileYear ft == 24 && getFileDep ft == K = k24
    | otherwise                                  = Null
    where
        -- 取得する列のヘッダー
        ws24  = T.pack "消費税の取扱い　"
        wk24  = T.pack "F137_消費税の取扱い"
        -- ヘッダーからインデックスを取り,値を取得
        s24text = projFrom ws24 hds tx
        k24text = projFrom wk24 hds tx
        --
        f :: Text -> Val
        f tx    | T.null tx               = Null
                | T.pack "1"    == tx     = VBool False
                | T.pack " "    == tx     = Null
                | T.pack "  "   == tx     = Null
                | T.pack "△"   == tx     = VBool True
                | otherwise               = error $ "fデータ変換_消費税記入の別: " ++ ushow tx

        s24 = f s24text
        k24 = f k24text

-- *** H事業別売上高
------------------------------------------------------------------

{- |
    * S24

        >    [集]ア農業、林業、漁業収入
        >    [集]イ鉱物、採石、砂利採取事業収入
        >    [集]ウ製造品の売上金額
        >    [集]エ㈰卸売販売額
        >    [集]エ㈪小売販売額
        >    [集]オ㈫建設事業収入
        >    [集]オ㈬電気、ガス、熱供給、水道事業収入
        >    [集]オ㈭通信、放送等事業収入
        >    [集]オ㈮運輸、郵便事業収入
        >    [集]オ㈯金融、保険事業収入
        >    [集]オ㉀政治・経済・団体活動収入
        >    [集]カ㈷情報サービス等事業収入
        >    [集]カ㉂不動産事業収入
        >    [集]カ㉃物品賃貸事業収入
        >    [集]カ㈹学術研究、専門・技術サービス事業収入
        >    [集]カ㈺宿泊事業収入
        >    [集]カ㈱飲食サービス事業収入
        >    [集]カ㈾生活関連サービス業、娯楽事業収入
        >    [集]カ㈴学習支援事業収入
        >    [集]カ㈲上記以外サービス事業収入
        >    [集]キ学校教育事業収入
        >    [集]ク医療、福祉事業収入
        >    [集]事業別売上金額不詳
    * S28

        >   補正＿ア１農業、林業、漁業の収入
        >   補正＿イ２鉱物、採石、砂利採取事業の収入
        >   補正＿ウ３製造品の出荷額・加工賃収入額／売上金額
        >   補正＿エ４卸売の商品販売額（代理・仲立手数料を含む）
        >   補正＿オ５小売の商品販売額
        >   補正＿カ６建設事業の収入（完成工事高）
        >   補正＿カ７電気、ガス、熱供給、水道事業の収入
        >   補正＿カ８通信、放送、映像・音声・文字情報制作事業の収入
        >   補正＿カ９運輸、郵便事業の収入
        >   補正＿カ１０金融、保険事業の収入
        >   補正＿カ１１政治・経済・文化団体の活動収入
        >   補正＿キ１２情報サービス、インターネット附随サービス事業の収入
        >   補正＿キ１３不動産事業の収入
        >   補正＿キ１４物品賃貸事業の収入
        >   補正＿キ１５学術研究、専門・技術サービス事業の収入
        >   補正＿キ１６宿泊事業の収入
        >   補正＿キ１７飲食サービス事業の収入
        >   補正＿キ１８生活関連サービス業、娯楽事業の収入
        >   補正＿キ１９社会教育、学習支援事業の収入
        >   補正＿キ２０上記以外のサービス事業の収入
        >   補正＿ク２１学校教育事業の収入
        >   補正＿ケ２２医療、福祉事業の収入
        >   補正＿事業別売上金額不詳  -}
{-# INLINE fデータ変換_事業別売上高 #-}
fデータ変換_事業別売上高 :: FileType -> HeaderTexts -> [Text] -> Val
fデータ変換_事業別売上高 ft hds tx
    | getFileDep ft == S  && getFileYear ft == 24 = s24
    | getFileDep ft == S  && getFileYear ft == 28 = s28
    | otherwise                                   = Null

    where
        -- 取得する列のヘッダー
        ws24   = s24事業別売上高
        ws28   = s28事業別売上高

        -- ヘッダーからインデックスを取り,値と分類番号を取得
        s24Values = getValues ws24 hds tx
        s24Names  = translateGoodsCodes  ws24 sd事業分類24
        s28Values = getValues ws28 hds tx
        s28Names  = translateGoodsCodes  ws28 sd事業分類28

        --
        s24 = textToValCars s24Values s24Names

        s28 = textToValCars s28Values s28Names

--  *** H輸出割合
------------------------------------------------------------------
-- | 製造業(K)だけで良い
-- * S 無視
-- * K24  F942_製造品出荷額等に占める直接輸出額の割合
-- * KMI28 出荷額等に占める直接輸出額割合
{-# INLINE fデータ変換_輸出割合 #-}
fデータ変換_輸出割合 :: FileType -> HeaderTexts -> [Text] -> ValDouble
fデータ変換_輸出割合 ft hds tx
    | ft == K24   = k24
    | ft == KMI28 = k28
    | otherwise   = Null
    where
        -- 取得する列のヘッダー
        wk24 = T.pack "F942_製造品出荷額等に占める直接輸出額の割合"
        wk28 = T.pack "出荷額等に占める直接輸出額割合"
        -- ヘッダーからインデックスを取り,値を取得
        k24text = projFrom wk24 hds tx
        k28text = projFrom wk28 hds tx
        --
        k24 = textToValDouble k24text
        k28 = textToValDouble k28text

--  *** H事業形態
------------------------------------------------------------------

{-# INLINE fデータ変換_事業形態 #-}
fデータ変換_事業形態 :: FileType -> HeaderTexts -> [Text] -> Val事業形態
fデータ変換_事業形態 ft hds tx
    | getFileYear ft == 24 && getFileDep ft == K = k24
    | getFileYear ft == 28 && getFileDep ft == K = Null
    | otherwise                                  = oth
    where
        -- 取得する列のヘッダー
        wk24  = T.pack "F104_経営組織"
        woth  = T.pack  "経営組織"
        -- ヘッダーからインデックスを取り,値を取得
        k24text = projFrom wk24 hds tx
        othtext = projFrom woth hds tx
        --
        f :: Text -> Val
        f tx    | tx  == T.pack "01" = V事業形態 E製造卸売
                | tx  == T.pack "02" = V事業形態 E製造遠隔小売
                | tx  == T.pack "03" = V事業形態 E加工
                | tx  == T.pack "04" = V事業形態 E自企業卸売
                | tx  == T.pack "05" = V事業形態 E他企業卸売
                | tx  == T.pack "06" = V事業形態 E製造小売
                | tx  == T.pack "07" = V事業形態 E店頭小売
                | tx  == T.pack "08" = V事業形態 E遠隔小売
                | tx  == T.pack "09" = V事業形態 E食品小売
                | tx  == T.pack "1"  = V事業形態 E製造卸売
                | tx  == T.pack "2"  = V事業形態 E製造遠隔小売
                | tx  == T.pack "3"  = V事業形態 E加工
                | tx  == T.pack "4"  = V事業形態 E自企業卸売
                | tx  == T.pack "5"  = V事業形態 E他企業卸売
                | tx  == T.pack "6"  = V事業形態 E製造小売
                | tx  == T.pack "7"  = V事業形態 E店頭小売
                | tx  == T.pack "8"  = V事業形態 E遠隔小売
                | tx  == T.pack "9"  = V事業形態 E食品小売
                | tx  == T.pack "10" = V事業形態 E料理配達
                | tx  == T.pack "11" = V事業形態 E土木
                | tx  == T.pack "12" = V事業形態 E建築
                | tx  == T.pack "13" = V事業形態 E工事
                | T.null tx          = Null
                | tx ==  T.pack " "  = Null
                | tx ==  T.pack "  " = Null
                | otherwise          = error $ "fデータ変換_事業形態 f 予期しない文字列: " ++ ushow tx

        k24 = f k24text
        oth = f othtext

--  *** H産業格付
------------------------------------------------------------------

-- | 作業で行うのでNull


{-# INLINE fデータ変換_産業格付     #-}
fデータ変換_産業格付 :: FileType -> HeaderTexts -> [Text] -> Val
fデータ変換_産業格付 ft hds tx = Null

--  *** H主な事業_事業所
------------------------------------------------------------------

{- |
    * S28

        >        [事]産業大分類
        >        [事]産業1.5分類
        >        [事]産業中分類
        >        [事]産業小分類
        >        [事]産業3.5分類
        >        [事]産業細分類
    * S24

        >        [事]産業大分類（最新）
        >        [事]産業1.5桁分類（最新）
        >        [事]産業中分類（最新）
        >        [事]産業3.5桁分類（最新）
        >        [事]産業小分類（最新）
        >        [事]産業細分類（最新）
    * K24

        >        F237_[事]産業大分類（最新）
        >        F238_[事]産業1.5桁分類（最新）
        >        F239_[事]産業中分類（最新）
        >        F240_[事]産業3.5桁分類（最新）
        >        F241_[事]産業小分類（最新）
        >        F242_[事]産業細分類（最新）
    * K28

        >        [事]産業大分類
        >        [事]産業1.5分類
        >        [事]産業中分類
        >        [事]産業小分類
        >        [事]産業3.5分類
        >        [事]産業細分類
    * KC28

        >       (事)産業大分類
        >       (事)産業1#5分類
        >       (事)産業中分類
        >       (事)産業小分類
        >       (事)産業3#5分類
        >       (事)産業細分類
    * KM28

        >        (事)産業大分類
        >        (事)産業1#5分類
        >        (事)産業中分類
        >        (事)産業小分類
        >        (事)産業3#5分類
        >        (事)産業細分類
    * KMI, KPI 無視

    * 1.5分類と,3.5分類は,それぞれ大分類,小分類と区別がつかないものがあるので,戦闘に "15#","35#" を足す


    -}

{-# INLINE fデータ変換_事前格付_事業所 #-}
fデータ変換_事前格付_事業所 :: FileType -> HeaderTexts -> [Text] -> Val産業格付
fデータ変換_事前格付_事業所 ft hds tx
    | getFileDep ft == S && getFileYear ft  == 24   = s24
    | getFileDep ft == S && getFileYear ft  == 28   = s28
    | ft == K24                                     = k24
    | ft == K28                                     = k28
    | ft == KC28                                    = kc28
    | ft == KM28                                    = km28
    | otherwise                                     = Null
    where
        -- 取得する列のヘッダー
        ws24   = ss28事前格付_事業所
        ws28   = ss24事前格付_事業所
        wk24   = sk24事前格付_事業所
        wk28   = sk28事前格付_事業所
        wkc28  = skc28事前格付_事業所
        wkm28  = skm28事前格付_事業所

        -- ヘッダーからインデックスを取り,値と分類番号を取得
        s24Values       = getTextValues       ws24   hds tx
        s28Values       = getTextValues       ws28   hds tx
        k24Values       = getTextValues       wk24   hds tx
        k28Values       = getTextValues       wk28   hds tx
        kc28Values      = getTextValues       wkc28  hds tx
        km28Values      = getTextValues       wkm28  hds tx

        -- Error
        -- とても素敵な"\\\"xx"か"\"x"か"\\"x"みたいな文字列(どれか分からん)が混じっているらしく
        -- これのCSVパーサ作成はやりたくない
        -- 一瞬で疲れ果てる．
        -- 神EXCELは神に任せる
        -- 汎用化できるならして

        killFuooooChar :: Text -> Text
        killFuooooChar tx   = T.filter (\x -> (x /= '"') && ( x /= '\\' )) tx

        f :: [Text] -> Val
        f xs | and (map (T.null) xs) = Null
             | otherwise = V産業格付
                         $ E産業格付    { _大分類  = xs !! 0
                                        , _15分類  = T.append (T.pack "15#") (killFuooooChar (xs !! 1))
                                        , _中分類  = xs !! 2
                                        , _小分類  = xs !! 3
                                        , _35分類  = T.append (T.pack "35#") (xs !! 4)
                                        , _細分類  = xs !! 5 }
        --
        s24  = f s24Values
        s28  = f s28Values
        k24  = f k24Values
        k28  = f k28Values
        kc28 = f kc28Values
        km28 = f km28Values

-- *** H主な事業_企業
------------------------------------------------------------------

{- |
    * S24

        >        [企]産業大分類（最新）
        >        [企]産業1.5桁分類（最新）
        >        [企]産業中分類（最新）
        >        [企]産業3.5桁分類（最新）
        >        [企]産業小分類（最新）
        >        [企]産業細分類（最新）
    * S28

        >        [企]産業大分類
        >        [企]産業1.5分類
        >        [企]産業中分類
        >        [企]産業小分類
        >        [企]産業3.5分類
    * K24

        >        F231_[企]産業大分類（最新）
        >        F232_[企]産業1.5桁分類（最新）
        >        F233_[企]産業中分類（最新）
        >        F234_[企]産業3.5桁分類（最新）
        >        F235_[企]産業小分類（最新）
        >        F236_[企]産業細分類（最新）
    * K28

        >        [企]産業大分類
        >        [企]産業1.5分類
        >        [企]産業中分類
        >        [企]産業小分類
        >        [企]産業3.5分類
    * KC28

        >       (企)産業大分類
        >       (企)産業1#5分類
        >       (企)産業中分類
        >       (企)産業小分類
        >       (企)産業3#5分類
    * KM, KMI, KPI 無視

    * 1.5分類と,3.5分類は,それぞれ大分類,小分類と区別がつかないものがあるので,戦闘に "15#","35#" を足す

    -}
{-# INLINE fデータ変換_事前格付_企業 #-}
fデータ変換_事前格付_企業 :: FileType -> HeaderTexts -> [Text] -> Val産業格付
fデータ変換_事前格付_企業 ft hds tx
    | getFileDep ft == S && getFileYear ft == 24   = s24
    | getFileDep ft == S && getFileYear ft == 28   = s28
    | ft == K24                                    = k24
    | ft == K28                                    = k28
    | ft == KC28                                   = kc28
    | otherwise                                    = Null
    where
        -- | 取得する列のヘッダー
        ws24   = ss24事前格付_企業
        ws28   = ss28事前格付_企業
        wk24   = sk24事前格付_企業
        wk28   = sk28事前格付_企業
        wkc28  = skc28事前格付_企業

        -- | ヘッダーからインデックスを取り,値と分類番号を取得
        s24Values       = getTextValues       ws24   hds tx
        s28Values       = getTextValues       ws28   hds tx
        k24Values       = getTextValues       wk24   hds tx
        k28Values       = getTextValues       wk28   hds tx
        kc28Values      = getTextValues       wkc28  hds tx


        --
        f24 :: [Text] -> Val
        f24 xs  | and (map (T.null) xs) = Null
                | otherwise = V産業格付
                            $ E産業格付 { _大分類  = xs !! 0
                                        , _15分類  = T.append (T.pack "15#") (xs !! 1)
                                        , _中分類  = xs !! 2
                                        , _小分類  = xs !! 3
                                        , _35分類  = T.append (T.pack "35#") (xs !! 4)
                                        , _細分類  = xs !! 5 }

        -- 28年からとってない
        f28 xs  | and (map T.null xs) = Null
                | otherwise  = V産業格付
                            $ E産業格付 { _大分類  = xs !! 0
                                        , _15分類  = T.append (T.pack "15#") (xs !! 1)
                                        , _中分類  = xs !! 2
                                        , _小分類  = xs !! 3
                                        , _35分類  = T.append (T.pack "35#") (xs !! 4)
                                        , _細分類  = T.empty }


        --
        s24  = f24 s24Values
        s28  = f28 s28Values
        k24  = f24 k24Values
        k28  = f28 k28Values
        kc28 = f28 kc28Values

-- *** H事業の種類
------------------------------------------------------------------

-- | SK24 : 主な事業の種類
--   SK28 : 主な事業の種類

{-# INLINE fデータ変換_事業の種類 #-}
fデータ変換_事業の種類 :: FileType -> HeaderTexts -> [Text] -> ValText
fデータ変換_事業の種類 ft hds tx
    | ft == SK24 || ft == SK28  = sk
    | otherwise  = Null
    where
        -- | 取得する列のヘッダー
        wsk = T.pack "主な事業の種類"
        skText  = textToDigitText $! projFrom wsk hds tx

        f tx | T.null tx         = Null
             | T.pack " "  == tx = Null
             | T.pack "  " == tx = Null
             | otherwise         = VText tx

        sk = f skText


-- *** H信用共済事業の有無
------------------------------------------------------------------


-- | VBool を返す
-- * S28 : 信用・共済事業の有無
-- * S24 : 信用事業又は共済事業の実施の有無
-- * K   : 項目なし

{-# INLINE fデータ変換_信用共済事業の有無 #-}
fデータ変換_信用共済事業の有無 :: FileType -> HeaderTexts -> [Text] -> Val
fデータ変換_信用共済事業の有無 ft hds tx
    | getFileYear ft == 24 && getFileDep ft == S = s24
    | getFileYear ft == 28 && getFileDep ft == S = s28
    | otherwise                                  = Null
    where
        -- | 取得する列のヘッダー
        ws24  = T.pack "信用事業又は共済事業の実施の有無"
        ws28  = T.pack "信用・共済事業の有無"

        -- | ヘッダーからインデックスを取り,値を取得

        s24text = projFrom ws24 hds tx
        s28text = projFrom ws28 hds tx
        --
        f :: Text -> Val
        f tx    | T.pack "1"   == tx    = VBool True
                | T.pack "2"   == tx    = VBool False
                | T.pack "△"  == tx    = Null
                | T.pack " "   == tx    = Null
                | T.pack "  "  == tx    = Null
                | T.null tx             = Null
                | otherwise             = error $ "fデータ変換_信用共済事業の有無: " ++ ushow tx

        s24 = f s24text
        s28 = f s28text

-- *** H協同組合の種類
------------------------------------------------------------------

-- |
-- * K  :: 項目なし
-- * S  :: 協同組合の種類
-- * ただし,24年,28年で回答形式が異なる
--
-- (28年は,その他の事業協同組合と事業協同組合が統合>>E事業協同組合として扱う)

{-# INLINE fデータ変換_協同組合の種類 #-}
fデータ変換_協同組合の種類 :: FileType -> HeaderTexts -> [Text] -> Val
fデータ変換_協同組合の種類 ft hds tx
    | getFileDep ft == S = s248
    | otherwise          = Null
    where
        -- | 取得する列のヘッダー
        ws  = T.pack "協同組合の種類"
        -- | ヘッダーからインデックスを取り,値を取得

        stext = projFrom ws hds tx
        --
        f :: Text ->  Val
        f tx    | tx  == T.pack "1"   = V協同組合の種類 E農業協同組合
                | tx  == T.pack "2"   = V協同組合の種類 E漁業協同組合
                | tx  == T.pack "3"   = V協同組合の種類 E水産加工協同組合
                | tx  == T.pack "4"   = V協同組合の種類 E森林組合
                | tx  == T.pack "5"   = V協同組合の種類 E事業協同組合
                | tx  == T.pack "6"   = V協同組合の種類 E協同組合以外
                | tx  == T.pack "7"   = V協同組合の種類 Eその他の事業協同組合
                | T.null tx           = Null
                | T.pack "  "  == tx  = Null
                | T.pack " "   == tx  = Null
                | otherwise           = error $ "fデータ変換_協同組合の種類 f 予期しない文字列: " ++ ushow tx

        s248 = f stext


-- *** H団体の種類
------------------------------------------------------------------

-- | S
-- * 28 全て 団体の種類
-- * SK24 建設サービスA 政治・経済・文化団体、宗教団体の団体種類
-- * K 項目なし

{-# INLINE fデータ変換_団体の種類 #-}
fデータ変換_団体の種類 :: FileType -> HeaderTexts -> [Text] -> Val
fデータ変換_団体の種類 ft hds tx
    | ft == SK24                                 = s24
    | getFileYear ft == 28 && getFileDep ft == S = s28
    | otherwise                                  = Null
    where
        -- | 取得する列のヘッダー
        ws24  = T.pack "政治・経済・文化団体、宗教団体の団体種類"
        ws28  = T.pack "団体の種類"
        -- | ヘッダーからインデックスを取り,値を取得

        s24text = projFrom ws24 hds tx
        s28text = projFrom ws28 hds tx

        --
        f :: Text -> Val
        f tx    | tx  == T.pack "1"   = V団体の種類 E政治団体
                | tx  == T.pack "2"   = V団体の種類 E経済団体
                | tx  == T.pack "3"   = V団体の種類 E労働団体
                | tx  == T.pack "4"   = V団体の種類 E学術団体文化団体
                | tx  == T.pack "5"   = V団体の種類 Eその他の団体
                | tx  == T.pack "6"   = V団体の種類 E神道系宗教
                | tx  == T.pack "7"   = V団体の種類 E仏教系宗教
                | tx  == T.pack "8"   = V団体の種類 Eキリスト教系宗教
                | tx  == T.pack "9"   = V団体の種類 Eその他の宗教
                | T.null tx           = Null
                | T.pack " "   == tx  = Null
                | T.pack "  "  == tx  = Null
                | otherwise         = error $ "fデータ変換_団体の種類 予期しない文字列: " ++ ushow tx

        s24 = f s24text
        s28 = f s28text

-- *** H8時間換算雇用者数_サB
-----------------------------------------------------------


{- |
    * SM28 ［事・サＢ］８時間換算雇用者数
    * K28 ［事・サＢ］８時間換算雇用者数
    * SM24 「飲食サービス業」の８時間換算雇用者数
-}
{-# INLINE fデータ変換_8時間換算雇用者数_サB #-}
fデータ変換_8時間換算雇用者数_サB :: FileType -> HeaderTexts -> [Text] -> Val
fデータ変換_8時間換算雇用者数_サB ft hds tx
    | ft == SM28  = sm28
    | ft == K28   = k28
    | ft == SM24  = sm24
    | otherwise   = Null
    where
        -- | 取得する列のヘッダー
        wsm28  = T.pack "［事・サＢ］８時間換算雇用者数"
        wk28   = T.pack "［事・サＢ］８時間換算雇用者数"
        wsm24  = T.pack "「飲食サービス業」の８時間換算雇用者数"

        -- | ヘッダーからインデックスを取り,値を取得
        sm28text  = projFrom wsm28   hds tx
        k28text   = projFrom wk28    hds tx
        sm24text  = projFrom wsm24   hds tx
        --
        sm28   = textToValDouble sm28text
        k28    = textToValDouble k28text
        sm24   = textToValDouble sm24text


-- *** H8時間換算雇用者数_商業
------------------------------------------------------------------

-- | VDouble
-- * S28    : ８時間換算雇用者数（卸・小）
-- * K24    : F132_８時間換算雇用者数(卸・小)
-- * KC28   : ８時間換算雇用者数（卸・小）
{-# INLINE fデータ変換_8時間換算雇用者数_商業 #-}
fデータ変換_8時間換算雇用者数_商業 :: FileType -> HeaderTexts -> [Text] -> Val
fデータ変換_8時間換算雇用者数_商業 ft hds tx
    | getFileYear ft == 28 && getFileDep ft == S  = s28
    | getFileYear ft == 24 && getFileDep ft == K  = k24
    | ft == KC28                                  = kc28
    | otherwise                                   = Null
    where
        -- | 取得する列のヘッダー
        ws28  = T.pack "８時間換算雇用者数（卸・小）"
        wk24  = T.pack "F132_８時間換算雇用者数(卸・小)"
        wkc28 = T.pack "８時間換算雇用者数（卸・小）"

        -- | ヘッダーからインデックスを取り,値を取得
        s28text  = projFrom ws28   hds tx
        k24text  = projFrom wk24   hds tx
        kc28text = projFrom wkc28  hds tx
        --
        s28   = textToValDouble s28text
        k24   = textToValDouble k24text
        kc28  = textToValDouble kc28text


-- *** H売場面積
-----------------------------------------------------------

{- |
    * K24 F1002_売場面積
    * KC28 ［事・卸小売］売場面積
-}
{-# INLINE fデータ変換_売場面積 #-}
fデータ変換_売場面積 :: FileType -> HeaderTexts -> [Text] -> ValDouble
fデータ変換_売場面積 ft hds tx
    | ft == K24   = k24
    | ft == KC28  = kc28
    | otherwise   = Null
    where
        -- | 取得する列のヘッダー
        wk24  = T.pack "F1002_売場面積"
        wkc28 = T.pack "［事・卸小売］売場面積"

        -- | ヘッダーからインデックスを取り,値を取得
        k24text  = projFrom wk24   hds tx
        kc28text = projFrom wkc28  hds tx
        --
        k24   = textToValDouble k24text
        kc28  = textToValDouble kc28text


-- *** Hセルフサービス
-----------------------------------------------------------

{- |
    * K24 F1001_セルフサービス方式の採用
    * KC28 セルフサービス方式の採用

    28年の定義書がないので，値の意味に関しては要確認
-}
{-# INLINE  fデータ変換_セルフサービス #-}
fデータ変換_セルフサービス :: FileType -> HeaderTexts -> [Text] -> ValBool
fデータ変換_セルフサービス ft hds tx
    | ft == KC28 = kc28
    | ft == K24  = k24
    | otherwise  = Null
    where
        -- | 取得する列のヘッダー
        wk24    = T.pack "F1001_セルフサービス方式の採用"
        wkc28   = T.pack "セルフサービス方式の採用"
        -- | 取得する列のヘッダーヘッダーからインデックスを取り,値を取得
        kc28text = projFrom wkc28 hds tx
        k24text  = projFrom wk24 hds tx
        --
        f :: Text -> Val
        f tx    | T.pack "1" == tx     = VBool True
                | T.pack "2" == tx     = VBool False
                | T.null tx            = Null
                | tx  == T.pack " "    = Null
                | tx  == T.pack "  "   = Null
                | otherwise            = error $ "fデータ変換_セルフサービス 予期しない文字列: " ++ ushow tx

        kc28 = f kc28text
        k24  = f k24text

-- *** H開店閉店期間
-----------------------------------------------------------

{- |
    * K24

        > F1003_営業時間の形態
        > F1004_開店時刻（午前・午後）
        > F1005_開店時刻（時）
        > F1007_閉店時刻（午前・午後）
        > F1008_閉店時刻（時）

    * KC28

        > 営業時間の形態
        > 開店時刻（午前・午後）
        > 開店時刻（時）
        > 閉店時刻（午前・午後）
        > 閉店時刻（時）

-}

{-# INLINE  fデータ変換_開店閉店期間 #-}
fデータ変換_開店閉店期間 :: FileType -> HeaderTexts -> [Text] -> ValInt
fデータ変換_開店閉店期間 ft hds tx
    | ft == KC28 = kc28
    | ft == K24  = k24
    | otherwise  = Null
    where
        -- 取得する列のヘッダー
        wkc28  = map T.pack
                [ "営業時間の形態"
                , "開店時刻（午前・午後）"
                , "開店時刻（時）"
                , "閉店時刻（午前・午後）"
                , "閉店時刻（時）"]

        wk24   = map T.pack
                [ "F1003_営業時間の形態"
                , "F1004_開店時刻（午前・午後）"
                , "F1005_開店時刻（時）"
                , "F1007_閉店時刻（午前・午後）"
                , "F1008_閉店時刻（時）"]


        -- ヘッダーからインデックスを取り,値を取得
        kc28text = getTextValues wkc28 hds tx
        k24text  = getTextValues wk24  hds tx
        --
        f :: [Text] -> Val
        f tx    | null tx                = Null
                | tx !! 0 == T.pack "2" = VInt 25
                | tx !! 1 /= tx !! 3     = VInt (12 + ((textToInt (tx !! 4)) - (textToInt (tx !! 2))))
                | tx !! 1 == tx !! 3     = VInt (((textToInt (tx !! 4)) - (textToInt (tx !! 2))))
                | otherwise              = Null

        kc28 = f kc28text
        k24  = f k24text


-- *** H商品形態
-----------------------------------------------------------

{- |
    * K24

    > F992_①衣料品
    > F993_②飲食料品
    > F994_③その他


    * KC28

    > ・衣料品
    > ・飲食料品
    > ・その他
-}
{-# INLINE  fデータ変換_商品形態 #-}
fデータ変換_商品形態 :: FileType -> HeaderTexts -> [Text] -> Val商品形態
fデータ変換_商品形態 ft hds tx
    | ft == KC28 = kc28
    | ft == K24  = k24
    | otherwise  = Null
    where
        -- 取得する列のヘッダー
        wk24  = map T.pack
                [ "F992_①衣料品"
                , "F993_②飲食料品"
                , "F994_③その他"]

        wkc28   = map T.pack
                [ "①衣料品"
                , "②飲食料品"
                , "③その他"]

        -- ヘッダーからインデックスを取り,値を取得
        k24text  = getValues wk24  hds tx
        kc28text = getValues wkc28 hds tx
        --
        f :: [Double] -> Val
        f tx    | null tx           = Null
                | L.length tx == 3  = V商品形態
                                    $ E商品形態 { _衣料品     = tx !! 0
                                                , _飲食料品   = tx !! 1
                                                , _その他商品 = tx !! 2 }
                | otherwise = Null

        kc28 = f kc28text
        k24  = f k24text



-- *** H販売形態
-----------------------------------------------------------

{- |
    * K24

    > F995_①店頭販売
    > F996_②訪問販売
    > F997_③通信・カタログ販売
    > F998_④インターネット販売
    > F999_⑤自動販売機による販売
    > F1000_⑥その他


    * KC28

    > ・店頭販売
    > ・訪問販売
    > ・通信・カタログ販売(インターネット以外)
    > ・インターネット販売
    > ・自動販売機による販売
    > ・その他


-}
{-# INLINE  fデータ変換_販売形態 #-}
fデータ変換_販売形態 :: FileType -> HeaderTexts -> [Text] -> Val販売形態
fデータ変換_販売形態 ft hds tx
    | ft == KC28 = kc28
    | ft == K24  = k24
    | otherwise  = Null
    where
        -- | 取得する列のヘッダー
        wk24  = map T.pack
                [ "F995_①店頭販売"
                , "F996_②訪問販売"
                , "F997_③通信・カタログ販売"
                , "F998_④インターネット販売"
                , "F999_⑤自動販売機による販売"
                , "F1000_⑥その他"]
        -- | 取得する列のヘッダー
        wkc28   = map T.pack
                [ "①店頭販売"
                , "②訪問販売"
                , "③通信・カタログ販売(インターネット以外)"
                , "④インターネット販売"
                , "⑤自動販売機による販売"
                , "⑥その他"]


        -- | ヘッダーからインデックスを取り,値を取得
        k24text  = getValues wk24  hds tx
        kc28text = getValues wkc28 hds tx
        --
        f :: [Double] -> Val
        f tx    | null tx           = Null
                | L.length tx == 3  = V販売形態
                                    $ E販売形態 { _店頭販売           = tx !! 0
                                                , _訪問販売           = tx !! 1
                                                , _通信販売           = tx !! 2
                                                , _インターネット販売 = tx !! 3
                                                , _自動販売機         = tx !! 4
                                                , _その他販売         = tx !! 5 }
                | otherwise = Null

        kc28 = f kc28text
        k24  = f k24text

-- *** H店舗形態
-----------------------------------------------------------

{- |
    * K24

    >  F1010_店舗形態

    * KC28

    >  店舗形態

-}

{-# INLINE  fデータ変換_店舗形態_商業 #-}
fデータ変換_店舗形態_商業  :: FileType -> HeaderTexts -> [Text] -> Val店舗形態_商業
fデータ変換_店舗形態_商業  ft hds tx
    | ft == KC28 = kc28
    | ft == K24  = k24
    | otherwise  = Null
    where
        -- | 取得する列のヘッダー
        wkc28  = T.pack "店舗形態"
        wk24   = T.pack "F1010_店舗形態"
        -- | ヘッダーからインデックスを取り,値を取得
        kc28text = projFrom wkc28 hds tx
        k24text = projFrom wk24  hds tx
        --
        f :: Text -> Val
        f tx    | T.pack "1" == tx     = V店舗形態_商業 E各種商品小売店
                | T.pack "2" == tx     = V店舗形態_商業 Eコンビニエンスストア
                | T.pack "3" == tx     = V店舗形態_商業 Eドラッグストア
                | T.pack "4" == tx     = V店舗形態_商業 Eホームセンター
                | tx  == T.pack " "    = Null
                | tx  == T.pack "  "   = Null
                | T.null tx            = Null
                | otherwise            = error $ "fデータ変換_店舗形態_商業 " ++ ushow tx

        kc28 = f kc28text
        k24  = f k24text


-- *** H事業収入_建設_サA
------------------------------------------------------------------

{- |
    * SK24

        > [建サＡ]分類番号１位
        > [建サＡ]分類番号２位
        > [建サＡ]分類番号３位
        > [建サＡ]分類番号４位
        > [建サＡ]分類番号５位
        > [建サＡ]分類番号６位
        > [建サＡ]分類番号７位
        > [建サＡ]分類番号８位
        > [建サＡ]分類番号９位
        > [建サＡ]分類番号10位
        > [建サＡ]売上（収入）金額１位
        > [建サＡ]売上（収入）金額２位
        > [建サＡ]売上（収入）金額３位
        > [建サＡ]売上（収入）金額４位
        > [建サＡ]売上（収入）金額５位
        > [建サＡ]売上（収入）金額６位
        > [建サＡ]売上（収入）金額７位
        > [建サＡ]売上（収入）金額８位
        > [建サＡ]売上（収入）金額９位
        > [建サＡ]売上（収入）金額10位

    * S28

        > [建サＡ]分類番号１位
        > [建サＡ]分類番号２位
        > [建サＡ]分類番号３位
        > [建サＡ]分類番号４位
        > [建サＡ]分類番号５位
        > [建サＡ]分類番号６位
        > [建サＡ]分類番号７位
        > [建サＡ]分類番号８位
        > [建サＡ]分類番号９位
        > [建サＡ]分類番号10位
        > 補正＿［建サＡ］売上（収入）金額１位
        > 補正＿［建サＡ］売上（収入）金額２位
        > 補正＿［建サＡ］売上（収入）金額３位
        > 補正＿［建サＡ］売上（収入）金額４位
        > 補正＿［建サＡ］売上（収入）金額５位
        > 補正＿［建サＡ］売上（収入）金額６位
        > 補正＿［建サＡ］売上（収入）金額７位
        > 補正＿［建サＡ］売上（収入）金額８位
        > 補正＿［建サＡ］売上（収入）金額９位
        > 補正＿［建サＡ］売上（収入）金額１０位

-}
{-# INLINE fデータ変換_事業収入_建サA #-}
fデータ変換_事業収入_建サA :: FileType -> HeaderTexts -> [Text] -> ValCars
fデータ変換_事業収入_建サA ft hds tx
    | ft == SK24   = s24
    | ft == SK28   = s28
    | otherwise    = Null
    where
        -- | 取得する列のヘッダー
        wsc24  = s24事業収入建サA番号 -- Classification
        wsv24  = s24事業収入建サA金額 -- Value

        wsc28  = s28事業収入建サA番号 -- Classification
        wsv28  = s28事業収入建サA金額 -- Value

        -- | ヘッダーからインデックスを取り,値と分類番号を取得
        s24Values       = getValues             wsv24 hds tx
        s24Names        = getDigitTextValues    wsc24 hds tx
        s28Values       = getValues             wsv28 hds tx
        s28Names        = getDigitTextValues    wsc28 hds tx

        s24             = textToValCars s24Values s24Names
        s28             = textToValCars s28Values s28Names


-- *** H工事種類
------------------------------------------------------------------

{- | SK◯◯ :: 工事種類1,工事種類2

-}

{-# INLINE fデータ変換_工事種類 #-}
fデータ変換_工事種類 :: FileType -> HeaderTexts -> [Text] -> Val工事種類
fデータ変換_工事種類 ft hds tx
    | ft == SK24   = sResult
    | ft == SK28   = sResult
    | otherwise    = Null
    where
        -- | 取得する列のヘッダー
        wsf = T.pack "工事種類１" -- 一番目
        wss = T.pack "工事種類２" -- 二番目
        -- | ヘッダーからインデックスを取り,値と分類番号を取得
        sfText = projFrom wsf hds tx
        ssText = projFrom wss hds tx

        sResult = V工事種類 $! E工事種類 sfText ssText


-- *** H金融業保険業の事業種類
------------------------------------------------------------------

-- | SK24 : 金融業、保険業、郵便局受託業の事業種類
--   SK28 : 金融業、保険業、郵便局受託業の事業種類

{-# INLINE fデータ変換_金融業保険業の事業種類 #-}
fデータ変換_金融業保険業の事業種類 :: FileType -> HeaderTexts -> [Text] -> ValText
fデータ変換_金融業保険業の事業種類 ft hds tx
    | ft == SK24   = sResult
    | ft == SK28   = sResult
    | otherwise    = Null
    where
        -- | 取得する列のヘッダー
        ws = T.pack "金融業、保険業、郵便局受託業の事業種類"

        -- | ヘッダーからインデックスを取り,値と分類番号を取得
        sText = projFrom ws hds tx
        sResult = VText $! textToDigitText sText


-- *** H店舗形態_サB
------------------------------------------------------------------

{- |
平成24，28年の事業所調査票（サービス関連産業B）においては，
サービス関連産業Bの事業収入内訳において，
産業分類中分類程度の区分での売上（収入）金額を聞いており，
調査項目「施設・店舗等形態」において，産業小分類程度の区分を聞いている．

11 ~ 74 の数字

SM24 : 施設・店舗等の形態番号
SM28 : 施設・店舗等形態


-}

{-# INLINE  fデータ変換_店舗形態_サB #-}
fデータ変換_店舗形態_サB :: FileType -> HeaderTexts -> [Text] -> ValText
fデータ変換_店舗形態_サB ft hds tx
    | ft == SM24  = sm24
    | ft == SM28  = sm28
    | otherwise   = Null
    where
        -- | 取得する列のヘッダー
        wsm24 = T.pack "施設・店舗等の形態番号"
        wsm28 = T.pack "施設・店舗等形態"

        sm24Text  = textToDigitText $! projFrom wsm24 hds tx
        sm28Text  = textToDigitText $! projFrom wsm28 hds tx

        f tx | T.null tx         = Null
             | T.pack " "  == tx = Null
             | T.pack "  " == tx = Null
             | otherwise         = VText tx

        sm24 = f sm24Text
        sm28 = f sm28Text


-- *** H事業収入_サB
------------------------------------------------------------------

{- |

    SM24

        > [サＢ]分類番号１位
        > [サＢ]分類番号２位
        > [サＢ]分類番号３位
        > [サＢ]分類番号４位
        > [サＢ]分類番号５位
        > [サＢ]分類番号６位
        > [サＢ]分類番号７位
        > [サＢ]分類番号８位
        > [サＢ]分類番号９位
        > [サＢ]分類番号10位
        > [サＢ]売上（収入）金額１位
        > [サＢ]売上（収入）金額２位
        > [サＢ]売上（収入）金額３位
        > [サＢ]売上（収入）金額４位
        > [サＢ]売上（収入）金額５位
        > [サＢ]売上（収入）金額６位
        > [サＢ]売上（収入）金額７位
        > [サＢ]売上（収入）金額８位
        > [サＢ]売上（収入）金額９位
        > [サＢ]売上（収入）金額10位

    SM28

        > [サＢ]分類番号１位
        > [サＢ]分類番号２位
        > [サＢ]分類番号３位
        > [サＢ]分類番号４位
        > [サＢ]分類番号５位
        > [サＢ]分類番号６位
        > [サＢ]分類番号７位
        > [サＢ]分類番号８位
        > [サＢ]分類番号９位
        > [サＢ]分類番号10位
        > 補正＿［サＢ］売上（収入）金額１位
        > 補正＿［サＢ］売上（収入）金額２位
        > 補正＿［サＢ］売上（収入）金額３位
        > 補正＿［サＢ］売上（収入）金額４位
        > 補正＿［サＢ］売上（収入）金額５位
        > 補正＿［サＢ］売上（収入）金額６位
        > 補正＿［サＢ］売上（収入）金額７位
        > 補正＿［サＢ］売上（収入）金額８位
        > 補正＿［サＢ］売上（収入）金額９位
        > 補正＿［サＢ］売上（収入）金額１０位




-}

{-# INLINE fデータ変換_事業収入_サB #-}
fデータ変換_事業収入_サB :: FileType -> HeaderTexts -> [Text] -> ValCars
fデータ変換_事業収入_サB ft hds tx
    | ft == SM24   = s24
    | ft == SM28   = s28
    | otherwise    = Null
    where
        -- | 取得する列のヘッダー
        wsc24  = s24事業収入サB番号 -- Classification
        wsv24  = s24事業収入サB金額 -- Value

        wsc28  = s28事業収入サB番号 -- Classification
        wsv28  = s28事業収入サB金額 -- Value

        -- | ヘッダーからインデックスを取り,値と分類番号を取得
        s24Values       = getValues             wsv24 hds tx
        s24Names        = getDigitTextValues    wsc24 hds tx
        s28Values       = getValues             wsv28 hds tx
        s28Names        = getDigitTextValues    wsc28 hds tx

        s24             = textToValCars s24Values s24Names
        s28             = textToValCars s28Values s28Names


-- *** H同業者割合_サB
------------------------------------------------------------------

{- |
SM24 : 同業者との契約割合
SM28 : 特定のサービス業における同業者との契約割合

-}

{-# INLINE fデータ変換_同業者割合 #-}
fデータ変換_同業者割合 :: FileType -> HeaderTexts -> [Text] -> ValDouble
fデータ変換_同業者割合 ft hds tx
    | ft == SM24   = s24
    | ft == SM28   = s28
    | otherwise   = Null
    where
        -- 取得する列のヘッダー
        ws24 = T.pack "同業者との契約割合"
        ws28 = T.pack "特定のサービス業における同業者との契約割合"

        -- ヘッダーからインデックスを取り,値を取得
        s24text  = projFrom ws24   hds tx
        s28text  = projFrom ws28  hds tx
        --
        s24   = textToValDouble s24text
        s28  = textToValDouble s28text

-- *** H事業所別生産物別売上高
-----------------------------------------------------------

-- | 元データには含まれないのでダミー
--
-- convertLine の時にNullを返すためだけに存在する
{-# INLINE fデータ変換_事業所別生産物別売上高 #-}
fデータ変換_事業所別生産物別売上高 :: FileType -> HeaderTexts -> [Text] -> Val
fデータ変換_事業所別生産物別売上高 ft hds tx = Null



------------------------------------------------------------------
-- * KMPの加工 出荷額,在庫額,加工賃収入 (28)年
------------------------------------------------------------------
-- | id のみでOrdが定義されるデータ型
data ForSort = FS {idtext :: Text, idx :: Int} deriving (Eq)
instance Ord ForSort where
    compare   x y     = compare   (idtext x) (idtext y)
    (<)       x y     = (<)       (idtext x) (idtext y)
    (<=)      x y     = (<=)      (idtext x) (idtext y)
    (>)       x y     = (>)       (idtext x) (idtext y)
    (>=)      x y     = (>=)      (idtext x) (idtext y)
    max x y | x >= y    = x
            | otherwise = y

    min x y | x <= y    = x
            | otherwise = y

-- | ForSortに変換して事業所番号でソートする

sortKMP :: IO ()
sortKMP = do
    tx <- readCSVWin (getRecordFilePath KMP28)
    let targetColIdx = Maybe.fromJust $ L.elemIndex (T.pack "事業所番号") hKMP28
        bd    = V.fromList tx
        bdCol = VDS.transpose tx
        targetCol = (L.!!) bdCol targetColIdx
        targetColForSort = L.zipWith (\x y -> FS x y) targetCol [0..]
        targetColSorted  = V.fromList $ L.map idx $ L.sort targetColForSort
        result = V.toList $ V.map ((V.!) bd) targetColSorted

    writeCSV "tempForSort.csv" result


forSyntax = 0 -- Syntax きれいにするためのもの,あとでけす


-- | 品目番号から,製造品,賃加工,製造業以外に分類するためのデータ型
data CommodityType  = Pr Text   -- ^ 製造品
                    | Elb Text  -- ^ 賃加工
                    | Oth Text  -- ^ 製造業以外
                    deriving (Eq)

-- | 品目番号から,製造品,賃加工,製造業以外に分類するための関数
{-# INLINE whichCommodityType #-}
whichCommodityType :: Text -> CommodityType
whichCommodityType tx | isElaboration tx  = Elb tx
                      | isOther       tx  = Oth tx
                      | otherwise         = Pr  tx
    where
    -- | 賃加工か否か判断する
    isElaboration :: Text -> Bool
    isElaboration tx | L.elem tx c商品分類賃加工 = True
                     | otherwise                 = False

    -- | 製造業以外か判断する
    isOther :: Text -> Bool
    isOther tx  | L.elem tx c商品分類製造業以外 = True
                | otherwise                     = False

{- | 出荷額,在庫額,加工賃,製造業以外KMP のみデータの構造が他と異なるため,別の処理を行う必要がある.
    事業所単位で,とれるもの以外はNullにしたデータを作成し,Header後に統合する.

     KMIは工業統計調査の商品分類に従って一行1商品でデータが構成されているので,事業所番号でソートして
    上から順に読み込み,事業所が変わったら一行書き込みを行う.


KMP28 を事業所番号でソート
Textとして取得 →ベクトル化


事業所番号を一列取得して,インデックスのペアをListのメソッドでソート
インデックスで取得



以下の,ヘッダー情報のみを持つcsvファイルを作成する.

    * H事業所番号
        > （28センサスキー）(確定)市区町村コード(所在地)
        > （28センサスキー）(確定)調査区番号（所在地）
        > （28センサスキー）(確定)事業所番号
        > （28センサスキー）(確定)＊コード

    * H出荷額_製造業

        > 品目番号
        > 出荷金額


    * H在庫額_製造業

        > 品目番号
        > 在庫金額

    * H収入額_加工賃

        > 品目番号
        > 出荷金額
    * H収入額_製造業以外

        > 品目番号
        > 出荷金額
    * H収入額_製造業以外
    VDC.c商品分類製造業以外 に含まれるか否かで判定. -}

convertKMP :: IO ()
convertKMP = do
    rHandle <- openFile "Data/Record/KMP28.csv" ReadMode
    wHandle <- openFile "Data/Record/KMP28Converted.csv"    WriteMode
    let cpWin = "cp932"

    tempNum     <- newIORef T.empty -- 事業所番号
    ship        <- newIORef V.empty  -- 出荷額
    stock       <- newIORef V.empty  -- 在庫額
    elb         <- newIORef V.empty  -- 加工賃
    oth         <- newIORef V.empty  -- 製造業以外の収入額


    -- cp <- mkTextEncoding cpWin
    -- hSetEncoding rHandle cp
    -- hSetEncoding wHandle cp

    let usedHd =    [ H事業所番号, H出荷額_製造業
                    , H在庫額_製造業 , H収入額_加工賃
                    , H収入額_製造業以外]
        notUsedHd = headerList L.\\ usedHd


        header  = T.concat
                $ (L.intersperse (T.pack ","))
                $ map (T.pack . ushow)
                $ usedHd ++ notUsedHd

    TO.hPutStrLn wHandle header
    loop rHandle wHandle tempNum elb oth ship stock
    hClose rHandle
    hClose wHandle

     ------------------------------------------------------------------
    where
     ------------------------------------------------------------------
     -- 事業所番号取得用
     ------------------------------------------------------------------
     censusIdHeaders   = L.map T.pack
                             [ "（28センサスキー）(確定)市区町村コード(所在地)"
                             , "（28センサスキー）(確定)調査区番号（所在地）"
                             , "（28センサスキー）(確定)事業所番号"
                             , "（28センサスキー）(確定)＊コード"]

     f1 x = if x == T.pack "" || x == T.pack "     " then T.pack "00000"  else x
     f2 x = if x == T.pack "" || x == T.pack "    "  then T.pack "0000"   else x
     f3 x = if x == T.pack "" || x == T.pack "    "  then T.pack "0000"   else x
     f4 x = if x == T.pack "" || x == T.pack " "     then T.pack "0"      else x
     fs  = [f1, f2, f3, f4]
     ------------------------------------------------------------------

     -- | 一行読み取って,値を読み解く
     -- * 事業所番号が変わったら書き込み & 更新
     loop   :: Handle -> Handle
            -> IORef Text
            -> IORef (Vector Car)
            -> IORef (Vector Car)
            -> IORef (Vector Car)
            -> IORef (Vector Car)
            -> IO ()
     loop rHandle wHandle tempNum elb oth ship stock = do
        eof         <- hIsEOF rHandle

        let output = do
                redGoodsId  <- (\x -> if T.null x then Null else VText x) <$> readIORef tempNum
                redShip     <- (\x -> if V.null  x then Null else VCars x) <$> readIORef ship
                redStock    <- (\x -> if V.null  x then Null else VCars x) <$> readIORef stock
                redElb      <- (\x -> if V.null  x then Null else VCars x) <$> readIORef elb
                redOth      <- (\x -> if V.null  x then Null else VCars x) <$> readIORef oth
                when (redGoodsId /= Null) $ hPutCsvLn wHandle
                                          $ (map (T.pack . ushow)
                                          [ redGoodsId, redShip, redStock, redElb , redOth])
                                          ++ replicate (length headerList - 5) (T.pack "Null")

        if eof
            then do output ; return ()
            else do
                line <- head <$> parseCSVErr <$> TO.hGetLine rHandle

                let currentNum = projFrom (T.pack "事業所番号") hKMP28 line  -- デフォルトの事業所番号

                    goodsId    = projFrom (T.pack "品目番号") hKMP28 line    -- 品目番号

                    stockVal   = textToDouble                                 -- 在庫金額
                               $ projFrom (T.pack "在庫金額") hKMP28 line

                    shipVal    = textToDouble                                 -- 出荷金額
                               $ projFrom (T.pack "出荷金額") hKMP28 line

                    censusId   = VText                                        -- 作成した事業所番号
                               $ T.concat
                               $ L.zipWith (\f x -> (f x)) fs
                               $ L.map (\x -> projFrom x line hKMP28) censusIdHeaders

                let ifIsNot0Snoc val x xs   = if val /= 0
                                                 then V.snoc xs (Car val x)
                                                 else xs


                    modifyChart name = case whichCommodityType name of
                                Elb x -> modifyIORef elb   (ifIsNot0Snoc shipVal  x)
                                Oth x -> modifyIORef oth   (ifIsNot0Snoc shipVal  x)
                                Pr  x -> modifyIORef ship  (ifIsNot0Snoc shipVal  x)
                                      >> modifyIORef stock (ifIsNot0Snoc stockVal x)


                redTempNum <- readIORef tempNum
                if redTempNum == currentNum
                    then modifyChart goodsId

                    else    output
                    >>      writeIORef  tempNum currentNum
                    >>      writeIORef  elb     V.empty
                    >>      writeIORef  oth     V.empty
                    >>      writeIORef  ship    V.empty
                    >>      writeIORef  stock   V.empty
                    >>      modifyChart goodsId

                loop rHandle wHandle tempNum elb oth ship stock

------------------------------------------------------------------
-- * データの統合
------------------------------------------------------------------

-- | 一行から読めるだけ情報をとって変換する関数
--

{-# INLINE convertLine #-}
convertLine :: FileType -> [Text] -> [Val]
convertLine ft tx   = runEval $ parMapStrict (\h -> convert h ft (getHeader ft) tx) headerList


-- | 元データからセンサスデータへの変換
-- * ファイルごとにセンサス形式に変更する
-- * 一行読み込み,一行書き出し
convertData :: FileType -> OutputFile ->  IO ()
convertData ft out = do
    rHandle <- openFile (getRecordFilePath ft) ReadMode
    wHandle <- openFile out       WriteMode

    -- 最初にHeaderを書き込む
    TO.hPutStrLn wHandle VDS.outputHeader
    loop rHandle wHandle
    hClose rHandle
    hClose wHandle

    where
    loop :: Handle -> Handle -> IO ()
    loop rHandle wHandle
        = hIsEOF rHandle >>= \eof
        -> case eof  of
            True  ->    return ()
            False ->    head
                        <$> parseCSVErr
                        <$> TO.hGetLine rHandle >>= \ !line
                        ->  CSV.hPutCsvLn wHandle (map  (T.pack . ushow) (convertLine ft line))
                        >>  loop rHandle wHandle


-- | ConvertDataのConduit版早くなるのかは要検証
convertDataConduit :: FileType -> OutputFile -> IO ()
convertDataConduit ft output
    =  openFile output WriteMode >>= \wHandle
    -> TO.hPutStrLn wHandle VDS.outputHeader
    >> runConduitRes ( sourceConvert  ft .| convertConduit ft.| unlinesTL .| VDS.sinkFileTL wHandle)

-- | 生産者
sourceConvert :: MonadResource m => FileType -> ConduitT a Text m ()
sourceConvert ft = CC.sourceFile (getRecordFilePath ft) .| CB.lines
                                                        .| CL.map E.decodeUtf8

-- | 消費者
convertConduit :: (Monad m, MonadIO m ) =>  FileType -> ConduitT Text Text m ()
convertConduit ft   =  await >>= \ maybeIcr
                    -> case maybeIcr of
                        Nothing   -> return ()
                        Just line -> yield (f ft line) >> convertConduit ft
    where
    f ft xs = T.concat.(L.intersperse (T.pack ",")).map CSV.toCsvText
            $ map (T.pack . ushow)
            $ g ft xs

    g ft = (convertLine ft) . L.head . parseCSVErr


convertWhole :: Year -> OutputFile -> IO ()
convertWhole year output = do
    let fileTypes = filter (\x -> getFileYear x == year) [SB28 .. KMI28]
    CMP.forM_ fileTypes $ \ fileType -> do
        let output = ((init.init.init.init)  (getRecordFilePath fileType)) ++ "Converted.csv"
        print $ "Converting " ++ show fileType ++ " ..."
        convertDataConduit fileType output
        print $ "Finished conversion of " ++ show fileType ++ "!"

    when (year == 28) (print "Start converting KMP ..." >> convertKMP)
    print "merging converted files .... "
    VDS.mergeFilesMemEfficient output year



