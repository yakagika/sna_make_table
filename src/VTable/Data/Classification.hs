

{-# LANGUAGE  TemplateHaskell
            , BangPatterns
            , StrictData
            , OverloadedStrings  #-}

{- |
        Module     : VTable.Data.Classification
        Copyright  : (c) Kaya Akagi. 2018-2019
        Maintainer : akagi15@cs.dis.titech.ac.jp


        必要なデータをIOとして扱うのが面倒なので,全てデータをこのモジュール内で定義するためのHaskell
        * 必要なデータが無かったため分類やシソーラスに関しては作者の自作.実際のコンバーター等とコードが異なる可能性があるため
        注意

        * 表記を統一するために日本語を使っているので、等幅フォント推奨
        * 量の多いデータはTemplate Haskell(TH)でコンパイル時に読み込む
        * エンコーディングに関して

            > 入出力も含めてすべて"BOMなしの"UTF-8で統一する(Shift-Jisは使わない)
            > Windowsでの起動は想定していないので，Dockerを利用して，Linux上で動かすこと
            > Docker for Windows を利用する場合はchcp 65001をしないとTemplateHaskell部分のコンパイルが通らない．

        * BOMに関して

        TemplateHaskell に読み込ませるデータをBOM付きにすると日本語の先端に点が入る．
        必ずBOMなしUTF-８で保存すること．メモ帳とエクセルは使わない．変換はnkfで．
-}


module VTable.Data.Classification where


import qualified    Data.Map.Strict                 as Map
import              Data.Map.Strict                 (Map)
import qualified    Data.Text                       as T
import              Data.Text                       (Text)
import qualified    Data.List                       as L
import              Data.Array.IArray
import qualified    Data.Char                       as Char


-- original Modules

import qualified VTable.Data.Structure              as VDS
import           VTable.Data.Structure
import           CSV.Text
import qualified CSV.Text                           as CSV

------------------------------------------------------------------
-- * Classification
------------------------------------------------------------------

--  産業分類を載せる

-- ** 商品分類
-- *** 賃加工
------------------------------------------------------------------

c商品分類賃加工 = CSV.getSingleCol $( loadCSV "Data/Classification/c商品分類賃加工.csv")

-- *** 製造業以外
------------------------------------------------------------------
-- | 24年,28年同じ

c商品分類製造業以外 = map T.pack [ "750000", "780000", "810000", "890000"]

-- *** 医療福祉
c医療福祉細分類コード = CSV.getSingleCol $( loadCSV "Data/Classification/c医療福祉細分類コード.csv")

-- *** 協同組合
c協同組合細分類コード = CSV.getSingleCol $( loadCSV "Data/Classification/c協同組合細分類コード.csv")

-----------------------------------------------------------
-- * g : 事業分類, 商品分類
-----------------------------------------------------------

-- *** サービスA，建設
-----------------------------------------------------------
gサービスA建設24 = CSV.getSingleCol $( loadCSV "Data/Classification/gサービスA建設24.csv")

gサービスA建設28 = CSV.getSingleCol $( loadCSV "Data/Classification/gサービスA建設28.csv")

-- | 商品分類の内建設業か判別する関数
is建設 :: Year ->  Text -> Bool
is建設 24 tx = L.elem tx (L.map (T.pack . show ) [301 .. 308 ])
is建設 28 tx = L.elem tx (L.map (T.pack . show ) [3401 .. 3410])
is建設 _  _  = error "is建設 can be applyied only to te Census 24, and 28."



-- | 元請か下請か判別する関数
is元請 :: Year -> Text -> Bool
is元請 24 tx = L.elem tx (L.map (T.pack . show ) [301,303,305,307])
is元請 28 tx = L.elem tx (L.map (T.pack . show ) [3401,3403,3404,3407,3409])
is元請 _  _  = error "is元請 can be applyied only to te Census 24, and 28."

-- *** サB
------------------------------------------------------------------

-- |  事業収入 店舗形態範囲事業
g事業収入_サB_店舗形態範囲24 = CSV.getSingleCol $( loadCSV "Data/Classification/g事業収入_サB_店舗形態範囲24.csv")

g事業収入_サB_店舗形態範囲28 = CSV.getSingleCol $( loadCSV "Data/Classification/g事業収入_サB_店舗形態範囲28.csv")

-- | 店舗形態範囲内か判別する関数
is店舗範囲 :: Year -> Text -> Bool
is店舗範囲 24 tx = L.elem tx g事業収入_サB_店舗形態範囲24
is店舗範囲 28 tx = L.elem tx g事業収入_サB_店舗形態範囲28
is店舗範囲 _  _  = error "is店舗範囲 can be applyied only to te Census 24, and 28."

-- | 事業収入 物品賃貸業
g事業収入_サB_物品賃貸業24 = map (T.pack . show) [1101 .. 1105]
g事業収入_サB_物品賃貸業28 = map (T.pack . show) [4101 .. 4110]

-- | 物品賃貸業か判定する関数
is物品賃貸業 :: Year -> Text -> Bool
is物品賃貸業 24 tx = L.elem tx g事業収入_サB_物品賃貸業24
is物品賃貸業 28 tx = L.elem tx g事業収入_サB_物品賃貸業28
is物品賃貸業 _  _  = error "is物品賃貸業 can be applyied only to te Census 24, and 28."



-- *** 商業
------------------------------------------------------------------
-- | 特殊な方法 卸売処理における財別と商品分類の内生産財
--
--  https://www.stat.go.jp/data/e-census/2016/kekka/pdf/r_shogyo.pdf
g卸売生産財 :: [Text]
g卸売生産財 = L.map T.pack ["511","532","533","534","535","536"]

-- | 特殊な方法 卸売処理における財別と商品分類の内資本財
g卸売資本財 :: [Text]
g卸売資本財 = L.map T.pack ["531","541","542","543","549"]

-- | 特殊な方法 卸売処理における財別と商品分類の内消費財
g卸売消費財 :: [Text]
g卸売消費財 = L.map T.pack ["512","513","521","522","551","552","553","559"]


data E財別 = E生産財 | E資本財 | E消費財
           deriving (Show, Eq, Ord)


-- | 3財以上含むかを判定するときに使う
ge卸売財別商品 :: Map Text E財別
ge卸売財別商品 = Map.fromList
              [(T.pack "511", E生産財)
              ,(T.pack "532", E生産財)
              ,(T.pack "533", E生産財)
              ,(T.pack "534", E生産財)
              ,(T.pack "535", E生産財)
              ,(T.pack "536", E生産財)
              ,(T.pack "531", E資本財)
              ,(T.pack "541", E資本財)
              ,(T.pack "542", E資本財)
              ,(T.pack "543", E資本財)
              ,(T.pack "549", E資本財)
              ,(T.pack "512", E消費財)
              ,(T.pack "513", E消費財)
              ,(T.pack "521", E消費財)
              ,(T.pack "522", E消費財)
              ,(T.pack "551", E消費財)
              ,(T.pack "552", E消費財)
              ,(T.pack "553", E消費財)
              ,(T.pack "559", E消費財)]



------------------------------------------------------------------
-- * Thesaurus
------------------------------------------------------------------
type Thesaurus = Map.Map Text Text



-- ** Survey -> Detail
------------------------------------------------------------------

-- | ストリングのタプルからレイジーテキストのマップを作る
toTextMap :: [(String,String)] -> Map Text Text
toTextMap xs = Map.fromList $ map (\(x,y) -> (T.pack x, T.pack y)) xs

-- *** 鉱業
-- |     24年
sd鉱業数量24 = CSV.getTwoColAsMap $(loadCSV "Data/Classification/sd鉱業数量24.csv")
sd鉱業金額24 = CSV.getTwoColAsMap $(loadCSV "Data/Classification/sd鉱業金額24.csv")

-- |     28年
sd鉱業数量28 = CSV.getTwoColAsMap $(loadCSV "Data/Classification/sd鉱業数量28.csv")
sd鉱業金額28 = CSV.getTwoColAsMap $(loadCSV "Data/Classification/sd鉱業金額28.csv")

-- *** 農林水産業
-- |     24年
sd農林漁業金額24 = CSV.getTwoColAsMap $(loadCSV "Data/Classification/sd農林漁業金額24.csv")
-- |   28年
sd農林漁業金額28 = CSV.getTwoColAsMap $(loadCSV "Data/Classification/sd農林漁業金額28.csv")

-- *** 学校教育
-- |     24年
sd学校教育24 =  CSV.getTwoColAsMap $(loadCSV "Data/Classification/sd学校教育24.csv")

-- |     28年
sd学校教育28 = CSV.getTwoColAsMap $(loadCSV "Data/Classification/sd学校教育28.csv")

-- *** 22区分事業分類
sd事業分類24 = CSV.getTwoColAsMap $( loadCSV "Data/Classification/sd事業分類24.csv")
sd事業分類28 = CSV.getTwoColAsMap $( loadCSV "Data/Classification/sd事業分類28.csv")

--- *** 収入額_製造業以外
-- |     28年のみ
sd収入額_製造業以外24 = CSV.getTwoColAsMap $( loadCSV "Data/Classification/sd収入額_製造業以外24.csv")

-- *** 物品賃貸業
------------------------------------------------------------------

sd物品賃貸業レンタル = CSV.getTwoColAsMap $( loadCSV "Data/Classification/sd物品賃貸業レンタル.csv")
sd物品賃貸業リース   = CSV.getTwoColAsMap $( loadCSV "Data/Classification/sd物品賃貸業リース.csv")


-- ** VDSにおけるEと細分類の変換
-----------------------------------------------------------

--- *** E事業所形態_医療福祉
-- | E事業所形態_医療福祉 と 産業細分類の対応関係
edE事業所形態_医療福祉 :: Map E事業所形態_医療福祉 IndustryDetail
edE事業所形態_医療福祉 =  Map.mapKeys parseE事業所形態_医療福祉
                       $! CSV.getTwoColAsMap
                       $( loadCSV "Data/Classification/edE事業所形態_医療福祉.csv")


--- *** E協同組合の種類
-- | E行動組合の種類 と 産業細分類の対応関係
edE協同組合の種類 :: Map E協同組合の種類 IndustryDetail
edE協同組合の種類 =  Map.mapKeys parseE協同組合の種類
                       $! CSV.getTwoColAsMap
                       $( loadCSV "Data/Classification/edE協同組合の種類.csv")


-- *** E団体の種類
-- | E団体の種類と 産業細分類の対応関係
edE団体の種類 :: Map E団体の種類 IndustryDetail
edE団体の種類 =  Map.mapKeys parseE団体の種類
                 $! CSV.getTwoColAsMap
                 $( loadCSV "Data/Classification/edE団体の種類.csv")


-- ** 商品分類，事業分類と細分類の変換
------------------------------------------------------------------
-- *** サービスA
-- | サービスAのみ（建設含まず） と 産業細分類の対応関係
gdサービスA24 :: Map Text Text
gdサービスA24 =  CSV.getTwoColAsMap $( loadCSV "Data/Classification/gdサービスA24.csv")


gdサービスA28 :: Map Text Text
gdサービスA28 = CSV.getTwoColAsMap $( loadCSV "Data/Classification/gdサービスA28.csv")

-- *** 建設
-- | 33分類と事業分類のマップ
gd建設 :: Map Text Text
gd建設 =  CSV.getTwoColAsMap $( loadCSV "Data/Classification/gd建設.csv")


-- *** 金融業、保険業、郵便局受託業の事業種類
-- | 金融業、保険業、郵便局受託業の事業種類 と産業細分類の対応関係
gd金融保険 :: Map Text Text
gd金融保険 =  CSV.getTwoColAsMap $( loadCSV "Data/Classification/gd金融保険.csv")


-- *** 学校教育
-- 学校等の種類の回答項目と 産業細分類の対応関係 (24年のみ)
gd学校教育24 :: Map Text Text
gd学校教育24 =  CSV.getTwoColAsMap $( loadCSV "Data/Classification/gd学校教育24.csv")

-- *** サービスA
-- | 主な事業の種類 と 産業細分類の対応関係 (24年)
gd主な事業の種類24 =  CSV.getTwoColAsMap $( loadCSV "Data/Classification/gd主な事業の種類24.csv")

-- | 主な事業の種類 と 産業細分類の対応関係 (28年)
gd主な事業の種類28 =  CSV.getTwoColAsMap $( loadCSV "Data/Classification/gd主な事業の種類28.csv")


-- *** 製造業
-- | 製造業(製造業以外) と 産業細分類の対応関係
--
-- 製造小売及び修理は,格付け不能に分類

gd製造業以外   = CSV.getTwoColAsMap $( loadCSV "Data/Classification/gd製造業以外.csv")


-- ** 調査項目 -> 調査項目
------------------------------------------------------------------
-- *** 建設業

-- | 建設業の調査項目と,調査項目の変換
ss建設分配24 :: Map Text [Text]
ss建設分配24 = getTwoColAsListMap
             $( loadCSV "Data/Classification/ss建設分配24.csv")


ss建設分配28 :: Map Text [Text]
ss建設分配28 = getTwoColAsListMap
             $( loadCSV "Data/Classification/ss建設分配28.csv")



-- | ss建設分配用の関数
getTwoColAsListMap :: Text -> Map Text [Text]
getTwoColAsListMap tx =  let xs = parseCSVErr tx
                      in let hd = head xs
                      in let bd = tail (CSV.transpose xs)
                      in Map.fromList $! L.zip hd bd

-- *** サB
-- | サB の事業収入と店舗形態の組み合わせで細分類に変換する
--
--   店舗形態と,事業収入の分類のPair と, 細分類のマップ
--
--   店舗形態の必要のないものは,店舗形態部分 T.empty

gdサB事業収入_店舗形態24 :: Map (Text, Text) Text
gdサB事業収入_店舗形態24   = getThreeColAsTupleMap
                           $( loadCSV "Data/Classification/gdサB事業収入_店舗形態24.csv")

gdサB事業収入_店舗形態28 :: Map (Text, Text) Text
gdサB事業収入_店舗形態28     = getThreeColAsTupleMap
                             $( loadCSV "Data/Classification/gdサB事業収入_店舗形態28.csv")



getThreeColAsTupleMap :: Text -> Map (Text, Text) Text
getThreeColAsTupleMap tx =  let xs = (parseCSVErr tx)
                      in Map.fromList
                      $! L.map
                      (\x -> ((x !! 0, x !! 1), x !! 2) )
                      xs



-- | 店舗形態がNullのVersion
gdサB事業収入_店舗形態無し24 :: Map Text Text
gdサB事業収入_店舗形態無し24  = CSV.getTwoColAsMap
                              $( loadCSV "Data/Classification/gdサB事業収入_店舗形態無し24.csv")

gdサB事業収入_店舗形態無し28 :: Map Text Text
gdサB事業収入_店舗形態無し28 = CSV.getTwoColAsMap
                             $( loadCSV "Data/Classification/gdサB事業収入_店舗形態無し28.csv")



-- | gdサB事業収入_店舗形 で想定された組み合わせ以外の場合．
gdサB事業収入_店舗形態不適合24 :: Map Text Text
gdサB事業収入_店舗形態不適合24 = CSV.getTwoColAsMap
                               $( loadCSV "Data/Classification/gdサB事業収入_店舗形態不適合24.csv")

gdサB事業収入_店舗形態不適合28 :: Map Text Text
gdサB事業収入_店舗形態不適合28 = CSV.getTwoColAsMap
                               $( loadCSV "Data/Classification/gdサB事業収入_店舗形態不適合28.csv")


--  *** 製造業
-- | 製造業出荷額の内,24年のみ
gd製造業24 = CSV.getTwoColAsMap $( loadCSV "Data/Classification/gd製造業24.csv")


-- ** 産業分類 -> 細分類
------------------------------------------------------------------
-- *** 商業
------------------------------------------------------------------
-- | 小売業と無店舗小売業の変換
dd無店舗小売業 = CSV.getTwoColAsMap $( loadCSV "Data/Classification/dd無店舗小売業.csv")

------------------------------------------------------------------
-- * 調査項目 s 年度 産業
------------------------------------------------------------------

-- *** 鉱業
------------------------------------------------------------------
-- | 平成24年鉱業
s24鉱業数量 = CSV.getSingleCol $( loadCSV "Data/Classification/s24鉱業数量.csv")

s24鉱業金額 = CSV.getSingleCol $( loadCSV "Data/Classification/s24鉱業金額.csv")


-- | 平成28年鉱業
s28鉱業数量 = getSingleCol $( loadCSV "Data/Classification/s28鉱業数量.csv")

s28鉱業金額 = getSingleCol $( loadCSV "Data/Classification/s28鉱業金額.csv")

-- *** 農林水産業
------------------------------------------------------------------
-- | 平成24年農林水産業
s24農林漁業金額 = getSingleCol $( loadCSV "Data/Classification/s24農林漁業金額.csv")

-- | 平成28年農林水産業
s28農林漁業金額 = getSingleCol $( loadCSV "Data/Classification/s28農林漁業金額.csv")

-- *** 商業
------------------------------------------------------------------
-- | 24年
s24商業分類 = getSingleCol $( loadCSV "Data/Classification/s24商業分類.csv")

s24商業金額 = getSingleCol $( loadCSV "Data/Classification/s24商業金額.csv")

s28商業分類 = getSingleCol $( loadCSV "Data/Classification/s28商業分類.csv")

s28商業金額 = getSingleCol $( loadCSV "Data/Classification/s28商業金額.csv")

-- *** 医療福祉
------------------------------------------------------------------
s24医療福祉 = getSingleCol $( loadCSV "Data/Classification/s24医療福祉.csv")

s28医療福祉 = getSingleCol $( loadCSV "Data/Classification/s28医療福祉.csv")

-- *** 製造業
------------------------------------------------------------------
s24製造業出荷分類    = getSingleCol $( loadCSV "Data/Classification/s24製造業出荷分類.csv")

s24製造業在庫金額    = getSingleCol $( loadCSV "Data/Classification/s24製造業在庫金額.csv")

s24製造業出荷金額    = getSingleCol $( loadCSV "Data/Classification/s24製造業出荷金額.csv")

s24製造業加工賃分類  = getSingleCol $( loadCSV "Data/Classification/s24製造業加工賃分類.csv")

s24製造業加工賃金額  = getSingleCol $( loadCSV "Data/Classification/s24製造業加工賃金額.csv")

s24製造業製造業以外  = getSingleCol $( loadCSV "Data/Classification/s24製造業製造業以外.csv")


-- *** 学校教育
------------------------------------------------------------------

s24学校教育 = getSingleCol $( loadCSV "Data/Classification/s24学校教育.csv")

s28学校教育 = getSingleCol $( loadCSV "Data/Classification/s28学校教育.csv")

-- *** 22区分 事業別売上高
------------------------------------------------------------------
s24事業別売上高 = getSingleCol $( loadCSV "Data/Classification/s24事業別売上高.csv")
s28事業別売上高 = getSingleCol $( loadCSV "Data/Classification/s28事業別売上高.csv")

-- *** 相手先別収入割合
------------------------------------------------------------------
s24相手先別収入割合_医療福祉 = getSingleCol $( loadCSV "Data/Classification/s24相手先別収入割合_医療福祉.csv")

s28相手先別収入割合_医療福祉 = getSingleCol $( loadCSV "Data/Classification/s28相手先別収入割合_医療福祉.csv")

s24相手先別収入割合_サB = getSingleCol $( loadCSV "Data/Classification/s24相手先別収入割合_サB.csv")

s28相手先別収入割合_サB = getSingleCol $( loadCSV "Data/Classification/s28相手先別収入割合_サB.csv")


-- *** レンタル
------------------------------------------------------------------
s24商品別レンタル売上高 = getSingleCol $( loadCSV "Data/Classification/s24商品別レンタル売上高.csv")

s28商品別レンタル売上高 = getSingleCol $( loadCSV "Data/Classification/s28商品別レンタル売上高.csv")

-- *** リース
------------------------------------------------------------------

s24商品別リース契約高  = getSingleCol $( loadCSV "Data/Classification/s24商品別リース契約高.csv")

s28商品別リース契約高  = getSingleCol $( loadCSV "Data/Classification/s28商品別リース契約高.csv")

-- *** 建設サービスA 事業収入
------------------------------------------------------------------
s24事業収入建サA番号 = getSingleCol $( loadCSV "Data/Classification/s24事業収入_建設サA番号.csv")
s24事業収入建サA金額 = getSingleCol $( loadCSV "Data/Classification/s24事業収入_建設サA金額.csv")

s28事業収入建サA番号 = getSingleCol $( loadCSV "Data/Classification/s28事業収入_建設サA番号.csv")
s28事業収入建サA金額 = getSingleCol $( loadCSV "Data/Classification/s28事業収入_建設サA金額.csv")


-- *** サB 事業収入
------------------------------------------------------------------
s24事業収入サB番号 = getSingleCol $( loadCSV "Data/Classification/s24事業収入_サB番号.csv")
s24事業収入サB金額 = getSingleCol $( loadCSV "Data/Classification/s24事業収入_サB金額.csv")

s28事業収入サB番号 = getSingleCol $( loadCSV "Data/Classification/s28事業収入_サB番号.csv")
s28事業収入サB金額 = getSingleCol $( loadCSV "Data/Classification/s28事業収入_サB金額.csv")

-- *** 事前格付
------------------------------------------------------------------

ss24事前格付_事業所    = getSingleCol $( loadCSV "Data/Classification/ss24事前格付_事業所.csv")

ss28事前格付_事業所    = getSingleCol $( loadCSV "Data/Classification/ss28事前格付_事業所.csv")

sk24事前格付_事業所    = getSingleCol $( loadCSV "Data/Classification/sk24事前格付_事業所.csv")

sk28事前格付_事業所    = getSingleCol $( loadCSV "Data/Classification/sk28事前格付_事業所.csv")

skc28事前格付_事業所   = getSingleCol $( loadCSV "Data/Classification/skc28事前格付_事業所.csv")

skm28事前格付_事業所   = getSingleCol $( loadCSV "Data/Classification/skm28事前格付_事業所.csv")

ss28事前格付_企業      = getSingleCol $( loadCSV "Data/Classification/ss28事前格付_企業.csv")

ss24事前格付_企業      = getSingleCol $( loadCSV "Data/Classification/ss24事前格付_企業.csv")

sk24事前格付_企業      = getSingleCol $( loadCSV "Data/Classification/sk24事前格付_企業.csv")

sk28事前格付_企業      = getSingleCol $( loadCSV "Data/Classification/sk28事前格付_企業.csv")

skc28事前格付_企業     = getSingleCol $( loadCSV "Data/Classification/skc28事前格付_企業.csv")

------------------------------------------------------
-- * Stratum and Industries
------------------------------------------------------

{- | 産業分類の階層

 総務省統計局HP「平成24年経済センサス‐活動調査 用語の解説 事業所の産業分類，企業産業分類」によれば，
 産業格付け作業では，各企業/事業所を，
 日本標準産業分類 に基づいた
 「大（1桁，20部門）
 ，1.5桁（2桁，29部門）
 ，中（2桁，113部門）
 ，小（3桁，548部門）
 ，3.5桁（3桁，607部門）
 ，細（4桁,1494部門）」
 の6段階における産業格付けを行っている．
 また，それらの分類とは別に記入表「事業別売上金額」における22区分の事業分類が存在し，
 更に調査票裏面において個別に内訳を調査する4~6桁の商品分類（製造業のみ）及び，
 建設業，商業などにおける独自の分類が存在する．本稿では，これらの分類を総称して以下，
 経済センサス分類と呼ぶ．

シンプルになるので22区分の事業分類も組み込む
-}

data Stratum    = Detail        -- ^ 細分類
                | TF            -- ^ 3.5分類 (Three Five)
                | Small         -- ^ 小分類
                | Middle        -- ^ 中分類
                | OF            -- ^ 1.5分類 (One Five)
                | Business      -- ^ 事業分類(22区分)
                | Large         -- ^ 大分類
                deriving (Show, Eq, Ord,Enum,Ix)

-- | 一つ上の階層を返す
{-# INLINE upStratum #-}
upStratum :: Stratum -> Maybe Stratum
upStratum = f
  where
  f Large    = Nothing
  f Business = Just Large
  f OF       = Just Business
  f Middle   = Just OF
  f Small    = Just Middle
  f TF       = Just Small
  f Detail   = Just TF

-- | 一つ下の階層を返す
{-# INLINE downStratum #-}
downStratum :: Stratum -> Maybe Stratum
downStratum = f
  where
  f Large    = Just Business
  f Business = Just OF
  f OF       = Just Middle
  f Middle   = Just Small
  f Small    = Just TF
  f TF       = Just Detail
  f Detail   = Nothing

-- | 産業分類の総称
type Industry         = Text
type IndustryLarge    = Text
type IndustryBusiness = Text
type IndustryOF       = Text
type IndustryMiddle   = Text
type IndustrySmall    = Text
type IndustryTF       = Text
type IndustryDetail   = Text
type IndustryV        = Text

-- | 下の階層の産業分類
type Lower  = Text

-- | 上の階層の産業分類
type Higher = Text

-- | Stratum と Idx :: Int で 産業分類を管理するArray
--
--

wholeIndMap :: Array (Stratum, Int) Industry
wholeIndMap = array ((Detail,0),(Large, numOf細分類))
            $! concat   [ largePart
                        , businessPart
                        , ofPart
                        , middlePart
                        , smallPart
                        , tfPart
                        , detailPart]
    where
    f :: Stratum -> [Text] -> [((Stratum,Int),Text)]
    f st xs = L.map (\x -> ((st, snd x), fst x)) $! L.zip xs [0 ..]
    largePart    = f Large      c大分類インデックス用
    businessPart = f Business   c22分類インデックス用
    ofPart       = f OF         c15分類インデックス用
    middlePart   = f Middle     c中分類インデックス用
    smallPart    = f Small      c小分類インデックス用
    tfPart       = f TF         c35分類インデックス用
    detailPart   = f Detail     c細分類インデックス用

-- * インデックス作成用重複データ
------------------------------------------------------------------
-- | 細分類ベースで,Index用に重複した大分類
c大分類インデックス用 = CSV.getSingleCol $( loadCSV "Data/Classification/c大分類インデックス用.csv")

-- | 細分類ベースで,Index用に重複した22分類
c22分類インデックス用 = CSV.getSingleCol $( loadCSV "Data/Classification/c22分類インデックス用.csv")

-- | 細分類ベースで,Index用に重複した1.5分類
c15分類インデックス用 = CSV.getSingleCol $( loadCSV "Data/Classification/c15分類インデックス用.csv")

-- | 細分類ベースで,Index用に重複した中分類
c中分類インデックス用 = CSV.getSingleCol $( loadCSV "Data/Classification/c中分類インデックス用.csv")

-- | 細分類ベースで,Index用に重複した小分類
c小分類インデックス用 = CSV.getSingleCol $( loadCSV "Data/Classification/c小分類インデックス用.csv")

-- | 細分類ベースで,Index用に重複した3.5分類
c35分類インデックス用 = CSV.getSingleCol $( loadCSV "Data/Classification/c35分類インデックス用.csv")

-- | 細分類ベースで,Index用に重複した細分類
c細分類インデックス用 = CSV.getSingleCol $( loadCSV "Data/Classification/c細分類インデックス用.csv")


-- ** インデックス
------------------------------------------------------------------
-- | 大分類インデックス
--
-- 重複するものは削除されている

ci大分類インデックス = Map.fromList $ L.zip  c大分類インデックス用 [0 ..]

-- | 22分類インデックス
--
-- 重複するものは削除されている

ci22分類インデックス = Map.fromList $ L.zip  c22分類インデックス用 [0 ..]

-- | 1.5分類インデックス
--
-- 重複するものは削除されている

ci15分類インデックス = Map.fromList $ L.zip  c15分類インデックス用 [0 ..]

-- | 中分類インデックス
--
-- 重複するものは削除されている

ci中分類インデックス = Map.fromList $ L.zip  c中分類インデックス用 [0 ..]

-- | 小分類インデックス
--
-- 重複するものは削除されている

ci小分類インデックス = Map.fromList $ L.zip  c小分類インデックス用 [0 ..]

-- | 3.5分類インデックス
--
-- 重複するものは削除されている

ci35分類インデックス = Map.fromList $ L.zip  c35分類インデックス用 [0 ..]

-- | 細分類インデックス
ci細分類インデックス = Map.fromList $ L.zip  c細分類インデックス用 [0 ..]




-- ** 産業分類
-----------------------------------------------------------

-- | 産業大分類
{-# INLINE c大分類 #-}
c大分類 :: [IndustryLarge]
c大分類 = CSV.getSingleCol $( loadCSV "Data/Classification/c大分類.csv")

{-# INLINE c大分類Map #-}
c大分類Map :: Map IndustryLarge Int
c大分類Map = Map.fromList $ L.zip c大分類 [0 ..]

-- | 産業22分類
{-# INLINE c22分類 #-}
c22分類 :: [IndustryBusiness]
c22分類 = CSV.getSingleCol $( loadCSV "Data/Classification/c22分類.csv")

{-# INLINE c22分類Map #-}
c22分類Map :: Map IndustryBusiness Int
c22分類Map = Map.fromList $ L.zip c22分類 [0 ..]

-- | 22分類 の数
numOf22分類 = L.length c22分類

-- | 1.5分類
{-# INLINE c15分類 #-}
c15分類 :: [IndustryOF]
c15分類 = CSV.getSingleCol $( loadCSV "Data/Classification/c15分類.csv")

{-# INLINE c15分類Map #-}
c15分類Map :: Map IndustryOF Int
c15分類Map = Map.fromList $ L.zip c15分類 [0 ..]


-- | 中分類
{-# INLINE c中分類 #-}
c中分類 :: [IndustryMiddle]
c中分類 = CSV.getSingleCol $( loadCSV "Data/Classification/c中分類.csv")

{-# INLINE c中分類Map #-}
c中分類Map :: Map IndustryMiddle Int
c中分類Map = Map.fromList $ L.zip c中分類 [0 ..]


-- | 小分類
{-# INLINE c小分類 #-}
c小分類 :: [IndustrySmall]
c小分類 = CSV.getSingleCol $( loadCSV "Data/Classification/c小分類.csv")

-- | 小分類 の数
numOf小分類 = L.length c小分類

{-# INLINE c小分類Map #-}
c小分類Map :: Map IndustrySmall Int
c小分類Map = Map.fromList $ L.zip c小分類 [0 ..]

-- | 3.5分類
{-# INLINE c35分類 #-}
c35分類 :: [IndustryTF]
c35分類 = CSV.getSingleCol $( loadCSV "Data/Classification/c35分類.csv")

-- | 3.5分類 Map
{-# INLINE c35分類Map #-}
c35分類Map :: Map IndustryTF Int
c35分類Map = Map.fromList $ L.zip c35分類 [0 ..]

-- | 細分類
{-# INLINE c細分類 #-}
c細分類 :: [IndustryDetail]
c細分類 = CSV.getSingleCol $( loadCSV "Data/Classification/c細分類.csv")


-- | 細分類の個数
numOf細分類 = L.length c細分類


{-# INLINE c細分類Map #-}
c細分類Map :: Map IndustryDetail Int
c細分類Map = Map.fromList $ L.zip c細分類 [0 ..]

-- | V表分類
{-# INLINE cV表分類 #-}
cV表分類 :: [IndustryV]
cV表分類 = CSV.getSingleCol $( loadCSV "Data/Classification/cV表分類.csv")

-- | V表分類の数
numOfV表分類 = L.length cV表分類

{-# INLINE cV表分類Map #-}
cV表分類Map :: Map IndustryV Int
cV表分類Map = Map.fromList $ L.zip cV表分類 [0 ..]



-- * Array 用のインデックス
------------------------------------------------------------------
{-# INLINE ci細分類インデックス正順 #-}
ci細分類インデックス正順 = Map.fromList $ L.zip  c細分類 [0 ..]
{-# INLINE ic細分類インデックス正順 #-}
ic細分類インデックス正順 = Map.fromList $ L.zip  [0 ..] c細分類

{-# INLINE ic小分類インデックス正順 #-}
ic小分類インデックス正順 = Map.fromList $ L.zip  [0 ..] c小分類
{-# INLINE ci小分類インデックス正順 #-}
ci小分類インデックス正順 = Map.fromList $ L.zip  c小分類 [0 ..]

{-# INLINE ic22分類インデックス正順 #-}
ic22分類インデックス正順 = Map.fromList $ L.zip  [0 ..] c22分類
{-# INLINE ci22分類インデックス正順 #-}
ci22分類インデックス正順 = Map.fromList $ L.zip  c22分類 [0 ..]


{-# INLINE icV表分類インデックス正順 #-}
icV表分類インデックス正順 = Map.fromList $ L.zip  [0 ..] cV表分類
{-# INLINE ciV表分類インデックス正順 #-}
ciV表分類インデックス正順 = Map.fromList $ L.zip  cV表分類 [0 ..]

-- ** 関数
-----------------------------------------------------------
-- | 産業分類のインデックスを取得する

{-# INLINE getIndIdx #-}
getIndIdx :: Industry -> Int
getIndIdx ind = case Map.lookup ind (selectMap (whichStratum ind)) of
                    Just num -> num
                    Nothing  -> error $ "error : getIndIdx, can not find \"" ++ T.unpack ind  ++ "\""
                    where
                    selectMap Large    = ci大分類インデックス
                    selectMap Business = ci22分類インデックス
                    selectMap OF       = ci15分類インデックス
                    selectMap Middle   = ci中分類インデックス
                    selectMap Small    = ci小分類インデックス
                    selectMap TF       = ci35分類インデックス
                    selectMap Detail   = ci細分類インデックス

-- | 任意の階層の産業分類を指定したStrutumに階層移動する
--
--  上から下は一位に定まらないので不可能

{-# INLINE elevateStratum #-}
elevateStratum :: Industry -> Stratum -> Maybe Industry
elevateStratum ind str  | indStratum <= str = Just $ wholeIndMap ! (str, indIdx)
                        | otherwise        = Nothing
                        where
                        indStratum = whichStratum ind
                        indIdx = getIndIdx ind

-- | 産業分類の階層を一つ上げる
{-# INLINE upInd #-}
upInd :: Industry -> Maybe Industry
upInd ind = case upStratum indStratum of
                Nothing  -> Nothing
                Just hig -> elevateStratum ind hig
                where indStratum = whichStratum ind

-- | Lower が Higherの下層分類か判定する

{-# INLINE isMemberOf #-}
isMemberOf :: Lower -> Higher -> Bool
isMemberOf low hig  | higStratum > lowStratum =  (elevateStratum low higStratum) == Just hig
                    | otherwise = False
                    where
                    higStratum = whichStratum hig
                    lowStratum = whichStratum low

{- | 与えられた産業分類の階層を返す

   Map とかで参照してもよいが,時間がかかるので,特徴で処理.

-}
{-# INLINE whichStratum #-}
whichStratum :: Industry -> Stratum
whichStratum ind    | isLarge    ind = Large
                    | isBusiness ind = Business
                    | isOF       ind = OF
                    | isMiddle   ind = Middle
                    | isSmall    ind = Small
                    | isTF       ind = TF
                    | isDetail   ind = Detail
                    | otherwise      = error $ "can not classify stratum " ++ T.unpack ind

-- 下の判定がちゃんと網羅しているかは要検証
{-# INLINE isLarge #-}
isLarge :: Industry -> Bool
isLarge tx = Map.member tx c大分類Map

{-# INLINE isBusiness #-}
isBusiness :: Industry -> Bool
isBusiness tx = Map.member tx c22分類Map

{-# INLINE isOF #-}
isOF :: Industry -> Bool
isOF tx  = Map.member tx c15分類Map

{-# INLINE isMiddle #-}
isMiddle :: Industry -> Bool
isMiddle tx = Map.member tx c中分類Map

{-# INLINE isSmall #-}
isSmall :: Industry -> Bool
isSmall tx = Map.member tx c小分類Map

{-# INLINE isTF #-}
isTF :: Industry -> Bool
isTF tx = Map.member tx c35分類Map

{-# INLINE isDetail #-}
isDetail :: Industry -> Bool
isDetail tx = Map.member tx c細分類Map

------------------------------------------------------------------
-- * 総務省 V表
------------------------------------------------------------------
-- | Small × V表分類
{-# INLINE cc小分類V表分類 #-}
cc小分類V表分類 :: Map Industry [Industry]
cc小分類V表分類 = Map.fromList
                $ L.map (\ x -> (L.head x, L.tail x))
                $ parseCSVErr  $( loadCSV "Data/Classification/cc小分類V表分類.csv")


------------------------------------------------------------------
-- * 管理補助的業務振替
------------------------------------------------------------------

-- | 管理補助的業務 小分類×小分類
ss管理補助的業務 :: Map Industry [Industry]
ss管理補助的業務 = Map.fromList
                $ L.map (\ x -> (L.head x, L.tail x))
                $ parseCSVErr  $( loadCSV "Data/Classification/ss管理補助的業務.csv")

------------------------------------------------------------------
-- * 格付け不能振替
------------------------------------------------------------------

-- | 格付け不能 細分類×細分類
ss格付け不能 :: Map IndustrySmall [IndustrySmall]
ss格付け不能 = Map.fromList
             $ L.map (\ x -> (L.head x, L.tail x))
             $ parseCSVErr $( loadCSV "Data/Classification/ss格付け不能.csv")


--  | 格付け不能Map 事業分類×細分類

bd格付け不能 :: Map IndustryBusiness IndustryDetail
bd格付け不能 =   CSV.getTwoColAsMap $(loadCSV "Data/Classification/bd格付け不能.csv")


