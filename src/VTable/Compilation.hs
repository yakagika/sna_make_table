
{-# LANGUAGE  BangPatterns, OverloadedStrings, StrictData, Strict, MultiWayIf #-}


{- |
      Module     : VTable.Compilation
      Copyright  : (c) Kaya Akagi. 2018-2019
      Maintainer : akagi15@cs.dis.titech.ac.jp

      V表作表のためのモジュール

      * 表記をマニュアルと統一するために日本語を使っているので,等幅フォント推奨
      * エンコーディングに関して

         > 入出力も含めてすべてUTF-8で統一する
         > Windowsでの起動は想定していないの，Dockerを利用して，Linux上で動かすこと
         > Docker for Windows を利用する場合はchcp 65001をしないとTemplateHaskell部分のコンパイルが通らない．

      * データ型の簡単な見方

      > f :: A -> B -> C
      > A と B を引数にとって，Cが返る．


      * 処理にメモリが足りないので，Conduit を用いて逐次処理を行っている．
-}



module VTable.Compilation where

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
import              Control.Monad
import              Control.Monad.ST
import              Control.DeepSeq
import              Data.STRef
import              Data.IORef
import              Data.Either
import              Data.Char
import              System.IO
import              System.Process
import              Text.Read
import              Debug.Trace
import              Control.Monad.IO.Class (liftIO, MonadIO)
import              Text.Show.Unicode               (ushow)
import              GHC.Err
import              GHC.Prim

--  for pararel
import              Control.Parallel.Strategies     hiding (parMap,(.|))
import              Control.Parallel
import qualified    Control.Monad.Parallel          as CMP

-- conduit
import              Data.Conduit
import qualified    Data.Conduit.List               as CL
import qualified    Data.Conduit.Binary             as CB hiding (sequence, dropWhile, sourceFile)
import qualified    Data.Conduit.Combinators        as CC


--  Original Modules
import qualified    CSV.Text                        as CSV
import              CSV.Text
import              VTable.Compilation.Conversion
import qualified    VTable.Compilation.Conversion   as VCC
import              VTable.Data.Structure
import qualified    VTable.Data.Structure           as VDS
import              VTable.Data.Classification
import qualified    VTable.Data.Classification      as VDC


-----------------------------------------------------------
-- * V表作成
-----------------------------------------------------------
{- |
 移行後S表の設計の議論に先立って，現行V表の推計手法を可能な限り詳細に検証する．

 「平成23年（2011年）産業連関表 総合解説編」によれば,V表は，平成17年まで工業統計調査，
 商業統計調査及び，サービス業基本調査を主に用いて推計されており，
 23年以降は対応する経済センサス- 活動調査の結果を主な資料として推計している．
 ただし，第13回産業連関技術会議資料 では，CTに関して17表以前に上記３つの統計以外から推計されていた農林水産，
 建設，金融などの部門においては，経済センサスデータを用いず，
 17年表以前の対応する基礎統計の値を国内総生産額（CT；Control Total）として用いているとの記述がある．
 平成23年産業連関表付帯表V表作成手順は大まかには以下のようになる．まず，経済センサス-活動調査の結果を用いて，
 産業別調査品目別売上額及び，産業別事業別売上額データを集計し，V表産業分類に合わせて分類の変換を行い，
 他の資料と併せて得られたCTをセンサス組替表より得られた比率で案分することで，一次推計値を作成する．

 その後，その一次推計値を各種統計資料によって係数を調整することで公表値が作成される．

 また，屑・副産物に関しては，取引基本表における屑・副産物発生部門をV表産業分類へ組替え，
 その値をセンサスから求められた産業×商品表の当該交点に計上している．

 このように，現行のV表の作成においては，主な資料として経済センサスを用いてはいるが，
 様々な統計調査の値が複合的に用いられている．本来であれば，現行V表の作成手法とは，
 それら利用される全ての基礎統計及びその利用方法をもれなく記載することとなるが，
 経済センサス以外の基礎統計の値を利用する処理に関する資料は少なく，また，作業も各省庁によって多岐に渡るため，
 その詳細を把握することは困難である．

 したがって，本稿では，それらの処理に関してまとめることはせず，可能な限り経済センサスを利用する部分にその対象を絞り，
 他の資料が利用されている点に関してはその旨を言及した上で，経済センサスを利用した代替的な推計手法を掲載する．
 これは，部分的にかけている推計手法では，全体像がつかみにくく，また，数値計算等を行う際に不具合が生じることにもよる．
 したがって，本稿では，以降，現行のV表の作成手法の調査に当たって可能な限り，資料に基づいた推測を行うが，
 ①資料の不足により詳細の把握できない箇所，②経済センサス以外の基礎統計をもとに推計されている個所，
 の２点に関しては，多分に筆者の憶測が含まれている点に留意して頂きたい．

 本稿ではV表の作成は大まかに，以下①~⑤の作業を想定している．
 なお，現行のV表の作成においては，屑，副産物の推計において取引基本表を経由しており，
 経済センサス以外の各種基礎統計値もその推計に利用している．
 本研究は，飽くまで同一データを利用することで推計手法毎の差異を分析することを目的としており，
 センサスデータから直接的に値を構成するという点で，推計手法が現行のものとは異なる．

 幾つかの補足できない概念等もそのまま未把握として扱い，大きな項目については他の統計を用いて簡易的に推計するなど，
 簡易的作成手法を採用する．

 ![V表推計手順図](procedure.png)
-}


compileVTable :: InputFile -> Double -> Year -> IO ()
compileVTable inputFile maxRowNum year =
    print "start first step "
    >> runConduitRes    (  sourceCensus inputFile
                        .| f在庫品評価調整
                        .| f産業格付_特殊な方法 year
                        .| f不適当分削除
                        .| f産業格付_一般的な方法 year
                        .| f価格変換 year
                        .| sinkCensus maxRowNum tmpFile)
    >> print "end first step. And start culculation of Industry weight map"
    >>  getWeightAndLink tmpFile                                                >>= \ (!iwm, !edm)
    ->  newIORef Map.empty                                                      >>= \ !empDenomiMap
    ->  runConduitRes (sourceCensus  tmpFile  .| getDenomiMap iwm empDenomiMap) >>= \ !denomi
    ->  newIORef Map.empty                                                      >>= \ !empToMakeMarginMap
    ->  newIORef []                                                             >>= \ !nullList
    ->  print "end second step. And start division"
    >>  runConduitRes   (sourceCensus tmpFile
                        .| f企業分割 iwm edm denomi
                        .| f商業マージン処理 empToMakeMarginMap nullList
                        .| f企業内取引削除 year
                        .| sinkCensus maxRowNum tmpFile2)
    >> print "culculating sub rate...."
    >> empSubRateArray                                                                              >>= \ !empSra
    -> runConduitRes ( sourceCensus  tmpFile2  .| f副業比率作成 empSra)                             >>= \ !sra
    -> print "dividing sub products...."
    >> runConduitRes ( sourceCensus  tmpFile2  .| f副業の分解 sra .| sinkCensus maxRowNum tmpFile3)
    >> print "culculating multipler...."
    >> newIORef Map.empty                                                                           >>= \ !emptmcm
    -> runConduitRes ( sourceCensus  tmpFile3  .| fCT乗数推計 emptmcm)                              >>= \ !ctm
    -> print "culculating table...."
    >> empICASmallDetail                                                                            >>= \ !empIca
    -> putStrLn "start f産業別生産物別産出額"
    >> runConduitRes ( sourceCensus  tmpFile3  .| f産業別生産物別産出額 ctm empIca)                 >>= \ !result細分類
    -> writeVTable "Data/Result/result細分類.csv" result細分類
    >> putStrLn "start f細分類振替"
    >> f細分類振替           result細分類                                                           >>= \ !result小分類
    -> writeVTable "Data/Result/result小分類.csv" result小分類
    >> putStrLn "start f管理補助的業務振替"
    >> f管理補助的業務振替   result小分類                                                           >>= \ !result小分類管理補助的業務なし
    -> writeVTable "Data/Result/result小分類管理補助的業務なし.csv" result小分類管理補助的業務なし
    >> putStrLn "start f格付け不能振替"
    >> f格付け不能振替       result小分類管理補助的業務なし                                         >>= \ !result小分類格付け不能振替
    -> fV表変換              result小分類格付け不能振替                                             >>= \ !result
    -> writeVTable resultFile result
    >> print "finished!!"

    where
    tmpFile     = "Data/Result/tempFile.csv"
    tmpFile2    = "Data/Result/tempFile2.csv"
    tmpFile3    = "Data/Result/tempFile3.csv"
    resultFile  = "Data/Result/resultTable.csv"



-----------------------------------------------------------
-- * 不適当分類削除
-----------------------------------------------------------
{- | 分類が微妙に異なるものを一つ一つ対応しきれないので，ここで強制的に処理する．

要修正 -}

f不適当分削除 :: (MonadIO m) => ConduitT IOCensusRow IOCensusRow m ()
f不適当分削除 = do
  maybeIcr <- await
  case maybeIcr of
    Nothing  -> return ()
    Just icr -> liftIO (readArray icr H事業所別生産物別売上高) >>= \ valComm
             -> case valComm of
                  Null        -> yield icr >> f不適当分削除
                  VCars comm  -> liftIO (f icr comm)
                              >> yield icr >> f不適当分削除
    where
    f :: IOCensusRow -> Cars -> IO ()
    f icr cs = do
        result <- newIORef V.empty
        V.forM_ cs $ \ c ->
            if | (VDC.isDetail.name) c -> modifyIORef result (V.cons c)
               | otherwise             -> liftIO (readArray icr H調査票の種類) >>= \ valKind
                                       -> putStrLn ( "調査票:" ++ (show valKind)
                                                   ++ "における, \n 事業所別生産物別売上高に含まれる以下の分類は細分類に当てはまるものがありません. " ++ show (name c))
        readIORef result >>= (writeArray icr H事業所別生産物別売上高) . VCars


-----------------------------------------------------------
-- * 在庫品評価調整
-----------------------------------------------------------

-- | ファイルを受け取って，在庫品評価調整を行って出力する
--
-- -N5 で３時間程度


full在庫品評価調整 :: InputFile -> Double -> IO ()
full在庫品評価調整 inputFile maxRowNum   = runConduitRes $ sourceCensus inputFile
                                                        .| f在庫品評価調整
                                                        .| sinkCensus maxRowNum outputFile
                                where
                                outputFile = (((init. init . init . init) inputFile) ++ "Stock.csv")

-- | 在庫品評価調整だけを行って出力する
--

f在庫品評価調整 :: (Monad m, MonadIO m ) => ConduitT IOCensusRow IOCensusRow m ()
f在庫品評価調整 = do
            maybeIcd <- await
            case maybeIcd of
                Nothing  -> return ()
                Just icd -> liftIO (f在庫品評価調整処理 icd)
                         >> yield icd
                         >> f在庫品評価調整


--  | 在庫品評価調整を行う関数
--
--    各事業所がどの調査票で調査されているかに応じて処理を変える
--    商業に関しては商業マージン推計で行うため，ここでは，処理しない

f在庫品評価調整処理 :: IOCensusRow -> IO ()
f在庫品評価調整処理 icd = do
        kind <- readArray icd H調査票の種類
        f在庫品評価調整_分岐 kind icd


-- | 在庫品評価調整における産業別の処理を調査票の種類に応じて分岐する関数
--

f在庫品評価調整_分岐 :: Val調査票の種類 -> IOCensusRow  -> IO ()
f在庫品評価調整_分岐 kind icd
    | kind == Null                      = return ()
    | _対象産業 (_調査票の種類 kind) == E農林漁業       = f在庫品評価調整_農林水産業       icd --  = return ()
    | _対象産業 (_調査票の種類 kind) == E鉱業           = f在庫品評価調整_鉱業             icd
    | _対象産業 (_調査票の種類 kind) == E製造業         = f在庫品評価調整_製造業           icd
    | _対象産業 (_調査票の種類 kind) == E商業           = f在庫品評価調整_商業             icd --  = return ()
    | _対象産業 (_調査票の種類 kind) == EサービスB      = f在庫品評価調整_出版ソフトウェア icd --  = return ()
    | _対象産業 (_調査票の種類 kind) == E建設サービスA  = f在庫品評価調整_建設業           icd --  = return ()
    | otherwise                         = return ()


-----------------------------------------------------------
-- ** 在庫品評価調整の調査票，産業別処理
-----------------------------------------------------------

-- 在庫品評価調整_農林水産業
-----------------------------------------------------------
{- |
    農林水産業に関して取得可能な売上金額は，主業は事業所調査票（農業，林業，漁業），
    企業調査票（農業，林業，漁業）の双方から得られる「事業別売上（収入）金額」における「農業，林業，漁業の収入」及び，
    裏面「農業，林業，漁業の収入の内訳」であり，共に売上（収入）金額が記入されているため，産出量の算出のためには，在庫品評価調整を必要とする．

    しかし，在庫，価格共にセンサス個票から推計することはできないため本稿では以降売上を算出として扱う．-}

f在庫品評価調整_農林水産業 :: IOCensusRow -> IO ()
f在庫品評価調整_農林水産業 cd = return ()


-- 在庫品評価調整_鉱業
-----------------------------------------------------------
{- |
    鉱業，採石業，砂利採取業に関しては，各種調査票表面「事業所別売上（収入）金額」では売上を記入するためこの値を用いる場合には，
    在庫品評価調整が必要となる．

    一方，事業所調査票（鉱業，採石業，砂利採取業）における裏面「生産数量及び生産金額」では，
    発生主義に基づく生産数量及び金額を調査しているため，裏面の情報に関しては在庫品評価調整を必要としない．

     従って，本稿では，可能な限り表面の情報を裏面の情報に置き換えるため，事業所調査票裏面の合計額と表面の額の比から，
     在庫品評価調整指数を作成し，それを副産物の推計の際に各従業の売上金額に乗じる処理を行う．
     このような処理が実際に行われているかは不明であるが，本稿では，センサス集計及び，組替集計にてこれを行うものとして設計する．-}

f在庫品評価調整_鉱業 :: IOCensusRow -> IO ()
f在庫品評価調整_鉱業 cd  =  readArray cd H事業別売上高   >>= \front
                         -> readArray cd H生産_鉱業_金額 >>= \back
                         -> convert cd front back
    where
    convert :: IOCensusRow -> ValCars -> ValCars ->  IO ()
    convert cd front back = case (front, back) of
        (VCars x, VCars y) ->     let !frontTotal = (V.sum . (V.map value) . (V.filter (\x -> name x == T.pack "T2"))) x
                              in  let !backTotal  = (V.sum . (V.map value)) y
                              in  let !r     = backTotal / frontTotal
                              in  let !newFront   = V.map (\ z  -> let v = value z in z {value = v * r} ) x
                              in  writeArray cd H事業別売上高 (VCars newFront)
        (_, _)             -> return ()



-- 在庫品評価調整_製造業
-----------------------------------------------------------
{- |
    製造業は従業に関しては，各種調査票の表面「事業別売上（収入）金額」で売上を聞いており，
    事業所調査票（製造業）裏面「製造品出荷額，在庫額等」では，「品目別製造品出荷額」及び「品目別製造品在庫額」を調査している．
    また，同裏面調査項目「製造品在庫額，半製品，仕掛品の価額及び原材料，燃料の在庫額」において，事業所全体の年初年末「製造品」，
    「半製品及び仕掛品」所有金額を調査している．

     これらの情報を利用して，製造業においては以下の処理を行う．

     製造業に関しては，製造品目が追記式であるため，表面の総和と裏面の総和が一致するとはかぎらないため，表面裏面それぞれで，処理を行う．

    * 表面

        >  年初年末製造品在庫額，半製品及び仕掛品在庫額から名目在庫変動を求め，
        > 名目在庫変動を売上高に足した総産出額を求める．

    * 裏面

        > 名目在庫額/年末製造品在庫額の比を求めてそれを，各品目別製造品在庫額に乗ずることで名目品目別在庫変動額を推計し，
        > それを品目別製造品出荷額に足すことで品目別製造品産出額を求める．-}

f在庫品評価調整_製造業 :: IOCensusRow -> IO ()
f在庫品評価調整_製造業 cd
    =  readArray    cd H年初製造品在庫額 >>= \first
    -> readArray    cd H年末製造品在庫額 >>= \final
    -> readArray    cd H事業別売上高     >>= \front
    -> readArray    cd H在庫額_製造業    >>= \stock
    -> readArray    cd H出荷額_製造業    >>= \output
    -> convertFront cd first final front
    >> convertBack  cd first final front stock output
    where
    convertFront  :: IOCensusRow
                  -> Val年初製造品在庫額
                  -> Val年末製造品在庫額
                  -> Val事業別売上高
                  -> IO ()
    convertFront cd  first final front = case (first, final, front) of -- 表面処理
        (VDouble x, VDouble y, VCars z) ->  do
            let newFront = (V.map (\car ->  let v = value car
                                            in  if name car == T.pack "T3" then car {value = v + (y - x)}
                                                                           else car )) z
            writeArray cd H事業別売上高 (VCars newFront)
        (_, _, _)                       -> return ()

    convertBack :: IOCensusRow
                -> Val年初製造品在庫額
                -> Val年末製造品在庫額
                -> Val事業別売上高
                -> Val在庫額_製造業
                -> Val出荷額_製造業
                -> IO ()
    convertBack cd first final front stock output
        =   case (first, final, front, stock, output) of -- 裏面処理
            (VDouble ft, VDouble fl, VCars fr, VCars st, VCars ou)  -> do
                let stockDiffRatio  = (fl - ft) / fl
                    mapSt = (Map.fromList . V.toList
                          .  (V.map (\x -> (name x, value x * stockDiffRatio)))) st
                    ouF x   =  let !toAdd = Map.lookup (name x) mapSt
                            in case toAdd of    Nothing -> x
                                                Just y  -> let v = value x in x {value = v + y}
                    newOu = V.map ouF ou
                    newSt = V.map (\x -> let !v = value x in x {value = v * (1 + stockDiffRatio)}) st

                writeArray cd H出荷額_製造業 (VCars newOu)
                writeArray cd H在庫額_製造業 (VCars newSt)

            (_, _, _, _, _) -> return ()



-- 在庫品評価調整_商業処理
-----------------------------------------------------------
{- |
    商業における在庫概念は，各種企業調査票における「商品売上原価」や，
    事業所調査票（卸売業，小売業）における裏面「（年末年初）商品手持額」によって調査されている．
    それら名目在庫処理の詳細は「4.6.1商業マージン」の推計を参照．-}

f在庫品評価調整_商業 :: IOCensusRow -> IO ()
f在庫品評価調整_商業 icd = return ()


-- 在庫品評価調整_出版ソフトウェア
-----------------------------------------------------------
{- |
    出版及び有形ソフトウェアは，在庫が計上されるが，
    経済センサスの調査項目からは把握できないため，ここでは，収入金額=産出金額として扱う．-}

f在庫品評価調整_出版ソフトウェア :: IOCensusRow -> IO ()
f在庫品評価調整_出版ソフトウェア cd = return ()

-- 在庫品評価調整_建設
-----------------------------------------------------------
{- |
    建設業は各種調査票「事業別売上（収入）金額」において主業，
    従業の総額を，「企業調査票（建設業，サービス関連産業A）」において主業の内訳を把握する．
    SNAにおける建設業は，完成工事高の他に，未完成工事高もその生産金額に含むがこれらの未完成工事高は経済センサスにおける調査項目では把握できない．
    したがって，本稿では建設業に関しては在庫品評価調整未完成工事高を含めない完成工事高分の売上額を生産額とみなして以後推計を行う．-}

f在庫品評価調整_建設業 :: IOCensusRow -> IO ()
f在庫品評価調整_建設業 cd = return ()



-----------------------------------------------------------
-- * 産業格付
-----------------------------------------------------------

-- | ファイルを受け取って，産業格付けを行った後出力
full産業格付 :: InputFile -> Double -> Year -> IO ()
full産業格付 inputFile maxRowNum year   = runConduitRes
                                        $ sourceCensus inputFile
                                        .| f産業格付_特殊な方法 year
                                        .| f不適当分削除
                                        .| f産業格付_一般的な方法 year
                                        .| sinkCensus maxRowNum outputFile
                                where
                                outputFile = (((init. init . init . init) inputFile) ++ "Classify.csv")



{- | 産業格付のみを行うConduit

    以降の処理で必要のない部門に関しては,データを削除する.

    経済センサスでは，産業毎に売上，従業者数や業態などの集計を行うため，
    その集計にあたって調査客体である企業/事業所各々の主業を定める作業を行う必要がある．

    この企業・事業所別の主業の策定作業を一般に「産業格付け」という．

    24年及び28年経済センサス調査票には，収入額，販売額とは別に「主な事業の内容」に関する調査項目が存在する．
    この「主な事業所」は，日本国内のすべての事業所・企業情報を補足する「事業所母集団データベース（ビジネスレジスター）」
    における事業所・企業照会，及び「事業の実施状況確認」をもとに事前に記載されており，
    変更のあった場合のみ調査票に各事業所が記載することとなっている．

    したがって，新規事業所を除いて各々の事業所は，調査段階で既に産業格付けがなされている．
    しかし，レストランやイベント会場を含んだホテル施設において，レストランの売り上げが，宿泊事業よりも収益が大きい場合など，
    事業所及び企業の認識する主な事業と「収入額または出荷額の最も多いもの」という産業格付けの原則が一致しないことがままある．
    このため，経済センサスの集計においては，各事業所を原則に則って再び産業格付けが行われている．

    産業格付けによる格付けは産業別の集計の際に用いられるが，
    組替集計のためには，主に調査票第２面で把握されている生産物別の売上額を把握し，
    事業所別生産物別生産量を把握する必要があり，そのためには，調査票で記載された各調査項目から，
    その事業所における主業の主生産物，副生産物を把握することが求められる．

    その際，裏面におえける各調査項目は，生産物と一対一対応にあるわけではないので，
    それぞれの調査項目から生産物及び売上額を特定する作業を必要とする．

    これらの処理は産業格付けにおける処理が参考となるため，ここでは産業格付けを行うと同時に，
    事業所別生産物別売上高が把握できるように設計する．

    全てIOにして,一行ずつ処理するほうが良い(要修正)
-}

f産業格付_特殊な方法 :: (Monad m, MonadIO m ) => Year -> ConduitT IOCensusRow IOCensusRow m ()
f産業格付_特殊な方法 year = do
    maybeIcd <- await
    case maybeIcd of
      Nothing  -> return ()
      Just icd -> liftIO (f産業格付_特殊な方法処理 year icd)
               >> yield icd
               >> f産業格付_特殊な方法 year

f産業格付_一般的な方法 :: (Monad m, MonadIO m ) => Year -> ConduitT IOCensusRow IOCensusRow m ()
f産業格付_一般的な方法 year = do
    maybeIcd <- await
    case maybeIcd of
      Nothing  -> return ()
      Just icd -> liftIO (f産業格付_一般的な方法処理 year icd)
               >> yield icd
               >> f産業格付_一般的な方法 year


-- ** 一般的な方法
-----------------------------------------------------------

{- | 売上高で産業格付けを行うため，マージン推計の前に行う．

    本稿では,この事業所別生産物別売上金額のデータを作成することを産業格付けにおける｢特殊な方法｣を利用して行い,
    作成された事業所別事業別売上金額の内最大のものを主業として選択することを｢一般的な方法｣としている(同時に従業,主生産物,副生産物が何であるかが判明する)。
    これらの方法を用いて決定された事業所別生産物別売上高及び産業格付けの分類項目を経済センサスにおける産業分類に変換し，
    産業別に集計することで産業別品目別の組替集計が完了する。


     「一般的な方法」は，以下の手続きに則って行われる。

    1. 事業別生産物別売上金額及び，事業別売上金額の最大売上部門を取得する。

    2. で決定した区分に該当する部門のみのデータを用いて，次点で細かい分類の最大売上区分を把握する。
     最大売上区分に重複がある場合には，双方において次点で細かい分類の最大売り上げ区分を把握し，その額の大きい方を採用する。

    3. それ以上細かい区分が存在しない場合は前段階区分における下位分類の「格付け不能」項目に分類する。
    重複があるのが最も細かい分類である場合は，識別番号の若い方を採用する。

     ![一般的な方法のワークフロー図](general.png)

    副業の分解は，副業の分解の項目で行う．

    政治・経済・文化団体には，協同組合の売り上げも含まれているので注意



-}

f産業格付_一般的な方法処理:: Year -> IOCensusRow -> IO ()
f産業格付_一般的な方法処理 year icd = do
        !en   <- readArray icd H事前格付_企業
        !es   <- readArray icd H事前格付_事業所
        !sev  <- readArray icd H事業別売上高
        !tar  <- readArray icd H事業所別生産物別売上高
        writeArray icd H産業格付 (f一般的な方法分岐 sev tar en es)

f一般的な方法分岐 :: Val事業別売上高
                  -> Val事業所別生産物別売上高
                  -> Val事前格付_企業
                  -> Val事前格付_事業所
                  -> Val産業格付
f一般的な方法分岐 Null Null en es = f事前格付処理 [] en es
f一般的な方法分岐 Null comm en es = f事業所別生産物別売上高処理 [] comm en es
f一般的な方法分岐 sev  Null en es = f事前格付処理 (f事業別売上金額最大項目取得 sev)  en es
f一般的な方法分岐 sev  comm en es = f事業所別生産物別売上高処理 (f事業別売上金額最大項目取得 sev) comm en es



-- | 事業別売上高の内最大の項目の産業分類を取得
f事業別売上金額最大項目取得 :: Val事業別売上高 ->  [Higher]
f事業別売上金額最大項目取得 Null          = []
f事業別売上金額最大項目取得 (VCars cs)    = VDS.vmaximumNamesWithoutErr
                                          $! V.filter (not . notSuiteCarName . name) cs

-- | 不適当な文字列に対する処理，Map使うと遅いので，とりあえず出てきたパターンに対応する
{-# INLINE notSuiteCarName #-}
notSuiteCarName tx  | T.null tx          = True
                    | T.any ('　' ==) tx = True
                    | T.any (' ' ==)  tx = True
                    | otherwise          = False

-- | 不適当な文字列に対する処理，Map使うと遅いので，とりあえず出てきたパターンに対応する
{-# INLINE convNotSuiteVal #-}
convNotSuiteVal :: ValCars -> ValCars
convNotSuiteVal Null        = Null
convNotSuiteVal (VCars cs)  = VCars $ convNotSuiteCars cs



convNotSuiteCars :: Cars -> Cars
convNotSuiteCars cs  = V.filter (\x -> not ((notSuiteCarName .name ) x)) cs


{- | 事前格付を利用した処理
企業調査票の産業格付けは企業産業分類という謎の分類を使用している
-}
------------------------------------------------------------------
f事前格付処理 :: [Higher] -> Val事前格付_企業 -> Val事前格付_事業所 -> Val産業格付
f事前格付処理 xs en es  | L.null xs = case (en,es) of
                                        (V産業格付 x, V産業格付 y)   -> V産業格付 (cov15and35 y)
                                        (Null,        V産業格付 y)   -> V産業格付 (cov15and35 y)
                                        (V産業格付 x, Null)          -> V産業格付 (cov15and35 x)
                                        (Null,        Null)          -> generalCNC

                        | otherwise = f産業格付補完 $! L.minimum xs
    where
    cov15and35 (E産業格付 l o m s t d) = E産業格付
                                        (conv Large l)
                                        (conv OF o)
                                        (conv Middle m)
                                        (conv Small s)
                                        (conv TF t)
                                        (conv Detail d)

    conv Large  ind = if isLarge  ind then ind else lemp
    conv OF     ind = if isOF     ind then ind else oemp
    conv Middle ind = if isMiddle ind then ind else memp
    conv Small  ind = if isSmall  ind then ind else semp
    conv TF     ind = if isTF     ind then ind else temp
    conv Detail ind = if isDetail ind then ind else demp


lemp = T.pack "△"         --  大分類格付け不可
oemp = T.pack "15#△△"    --  1.5分類格付け不可
memp = T.pack "△△"       --  中分類格付け不可
semp = T.pack "△△△"     --  小分類格付け不可
temp = T.pack "35#△△△"  --  3.5分類格付け不可
demp = T.pack "△△△△"   --  細分類格付け不可


-- | 事業内容等不詳
generalCNC = V産業格付  $! E産業格付 lemp oemp memp semp temp demp

-- | 与えられた最下層産業分類を利用して,産業格付を埋める
f産業格付補完 :: Industry -> Val産業格付
f産業格付補完 ~ind  | notSuiteCarName ind            = generalCNC
                    | indStratum == Large     = V産業格付 $! E産業格付 ind oemp memp semp temp demp
                    | indStratum == Business  = V産業格付 $! E産業格付 l   oemp memp semp temp demp
                    | indStratum == OF        = V産業格付 $! E産業格付 l   ind  memp semp temp demp
                    | indStratum == Middle    = V産業格付 $! E産業格付 l   o    ind  semp temp demp
                    | indStratum == Small     = V産業格付 $! E産業格付 l   o    m    ind  temp demp
                    | indStratum == TF        = V産業格付 $! E産業格付 l   o    m    s    ind  demp
                    | indStratum == Detail    = V産業格付 $! E産業格付 l   o    m    s    t    ind
    where
    ~indStratum = whichStratum ind

    f :: Industry -> Stratum -> Industry
    f ~x ~s =  case elevateStratum x s of
                Just x  -> x
                Nothing -> f demp s

    ~l = f ind Large
    ~o = f ind OF
    ~m = f ind Middle
    ~s = f ind Small
    ~t = f ind TF


-- | 事業所別生産物別売上高の内最大の項目の産業分類を取得
--
--   産業分類に謎のものが混ざっていたらここで除去する


f事業所別生産物別売上高処理 :: [Text]
                            -> Val事業所別生産物別売上高
                            -> Val事前格付_企業
                            -> Val事前格付_事業所
                            -> Val産業格付
f事業所別生産物別売上高処理 xs Null       en es = f事前格付処理 xs en es
f事業所別生産物別売上高処理 xs (VCars cs) en es = let csSafe
                                                = V.map (\x -> if (notSuiteCarName.name) x then x {name = (T.pack "△△△△")} else x) cs
                                                in let looped = f前段階売上区分内処理 xs cs
                                                in case L.length looped  of
                                                    0 ->     f事前格付処理 xs en es
                                                    1 ->     f産業格付補完 $! L.head looped
                                                    _ ->     f最下層格付処理 xs cs en es

-- | 一般的な方法の繰り返し部分
--
--   事業所別生産物別売上高には最下層以外はない
--
{-# INLINE f前段階売上区分内処理 #-}
f前段階売上区分内処理 :: [Higher] {- ^事業分類で与えられた,最大区分 -}
                      -> Cars
                      -> [Industry]
f前段階売上区分内処理 []   cs     | V.null cs = []
                                  | otherwise = f前段階売上区分内処理 (V.toList (V.map name (convToStratum cs Business))) cs -- 事業別売上高が存在しない場合の分岐
f前段階売上区分内処理 higs cs     = f OF higs cs -- 事業別売上高が存在した場合の分岐
    where
    -- | 一つ上の区分が存在する場合の処理
    f :: Stratum -> [Higher] -> Cars -> [Industry]
    f Detail xs  cs = let tmpCs = filtSelect xs cs in case L.null tmpCs of
                        True  -> xs
                        False -> VDS.vmaximumNamesWithoutErr tmpCs

    f st     xs  cs = let tmpCs = filtSelect xs (convToStratum cs st) in case L.null tmpCs of
                        True  -> xs
                        False -> f ((Maybe.fromJust . VDC.downStratum) st) (VDS.vmaximumNamesWithoutErr tmpCs) cs

--  | 与えられたStratumにCarsを変換統合する
{-# INLINE convToStratum #-}
convToStratum :: Cars -> Stratum -> Cars
convToStratum ~cs ~st = mergeSameNameCars
                    $! V.map Maybe.fromJust
                    $! V.filter Maybe.isJust
                    $! V.map (elevateStratumOfCar st) cs
    where
    elevateStratumOfCar :: Stratum -> Car -> Maybe Car
    elevateStratumOfCar ~st ~ca = case (elevateStratum (name ca) st) of
                            Just x   -> Just (ca {name = x})
                            Nothing  -> Nothing

-- |  指定された産業分類の下位分類だけでfilterをかける
{-# INLINE filtSelect #-}
filtSelect :: [Higher] -> Cars -> Cars
filtSelect ~xs ~cs = let g ~hig = V.filter (\c -> isMemberOf (name c) hig || name c == hig ) cs
                   in V.concat $! L.map g xs


-- | 最下層に行っても,重複があった場合の処理
f最下層格付処理 :: [Text] -> Cars -> Val事前格付_企業 -> Val事前格付_事業所 -> Val産業格付
f最下層格付処理 xs cs en es | L.null   xs      = generalCNC
                            | L.length xs == 1 = f産業格付補完 $! L.head xs
                            | L.length xs >= 2 = f事前格付処理 xs en es


------------------------------------------------------------------
-- ** 特殊な方法
------------------------------------------------------------------
{- | 調査票の種類に応じて以下の個別の処理を行う

     * 管理補助的業務及び，格付け不能もそれぞれの処理で行う．

     事業所調査票における調査項目「管理・補助的業務」では，
     もっぱら「管理・補助的業務」を行っている場合にその内容に関して「管理運営業務，補助的業務，自家用倉庫」から選択する形式となっている．

     当該調査項目において，「管理運営業務」が選択されていた場合は，
     一般的な方法において選択された産業区分と最も近い区分の「主として管理事務を行う本社等」，
    「補助的業務」が選択されていた場合は「その他の管理，補助的経済活動を行う事業所」に格付けし，
     双方が選択されていた場合は「管理，補助的経済活動を行う事業所 内格付け不能」とする．

     また，特殊な方法及び一般的な方法の結果，卸売業，小売業に区分された事業所において，
     「自家用倉庫」が選択されていた場合，最も近い「自家用倉庫」に格付けする．

     卸売業，小売業以外で「自家用倉庫」が選択されていた場合は「その他の管理，補助的経済活動を行う事業所」に格付けする．


    * 格付け不能の扱い

    「○○ 内格付不能」に格付けされた事業所に関しては，その属する産業分類に格付けされた，
    他の事業所の平均的な事業所別生産物売上高で，事業別売上高の当該項目の額を按分する．

    f産業格付_特殊な方法_全般 では，個別の処理をすべて統合する．
    各調査票，産業の処理は個別の関数 f産業格付_特殊な方法_〇〇産業 を調整すること．

-}


f産業格付_特殊な方法処理 :: Year -> IOCensusRow -> IO ()
f産業格付_特殊な方法処理 year icd = do
    f産業格付_特殊な方法_農林漁業     year icd
    f産業格付_特殊な方法_鉱業         year icd
    f産業格付_特殊な方法_製造業       year icd
    f産業格付_特殊な方法_商業         year icd
    f産業格付_特殊な方法_医療福祉          icd
    f産業格付_特殊な方法_サB          year icd
    f産業格付_特殊な方法_協同組合          icd
    f産業格付_特殊な方法_建サA        year icd
    f産業格付_特殊な方法_その他       year icd


-----------------------------------------------------------
-- *** 管理補助的業務に対応する関数
-----------------------------------------------------------

-- | 商業か否か
type IsCommerce = Bool

{- | E管理補助的業務 に応じて，対応する管理補助的業務の細かい分類を返す関数を作成する関数

    事業所調査票における調査項目「管理・補助的業務」では，
    もっぱら「管理・補助的業務」を行っている場合にその内容に関して「管理運営業務，補助的業務，自家用倉庫」から選択する形式となっている．
    当該調査項目において，「管理運営業務」が選択されていた場合は，
    一般的な方法において選択された産業区分と最も近い区分の「主として管理事務を行う本社等」，
    「補助的業務」が選択されていた場合は「その他の管理，補助的経済活動を行う事業所」に格付けする．
    また，特殊な方法及び一般的な方法の結果，卸売業，小売業に区分された事業所において，「自家用倉庫」が選択されていた場合，
    最も近い「自家用倉庫」に格付けする．
    卸売業，小売業以外で「自家用倉庫」が選択されていた場合は「その他の管理，補助的経済活動を行う事業所」に格付けする．


    * 主として管理事務を行う本社等

        > 下二桁が00
        > 非営利団体には存在しない

    * その他の管理，補助的経済活動を行う事業所

        > 下二桁が09
        > ただし，商業のみ08

    * 管理，補助的経済活動を行う事業所 内格付不能

        > 下２桁が0Z
        > ただし，これに分類される条件が不明なため使用しない
        > 0609
        > 0709
        > 0809
        > 7109
        > 7209
        > 7409
        > 7809
        > 784Z
        > 801Z
        > 8609
        > 8909
        > 9400
        > 9509 など存在しない項目も扱いが不明なため,機械的に分類を追加して処理を行った

    * 自家用倉庫

        > 下２桁が08

    * 産業内格付け不能の場合

        > 産業内格付け不能は下２桁がZZ
        > 格付不能は格付け不能のまま処理する（実際にどのようにしているのか調べる必要あり）
        > 784Z 恐らく公衆浴場格付け不能 及び 801Z 映画館格付け不能(?)の2項目に関しては追加し公衆浴場及び映画館として扱う

    ZZ と Z0等末尾が統一されていないので注意(要修正)
-}

{-# INLINE makeManagementClass #-}
makeManagementClass :: IsCommerce -> Val管理補助的業務 -> Text -> Text
makeManagementClass = f
    where

    -- | 格付け不能の対策
    g :: Text -> Text -> Text
    g tx1 tx2  = case T.drop 2 tx1 == T.pack "Z0" || T.drop 2 tx1 == T.pack "ZZ" of
                    True  ->  tx1
                    False ->  T.append (T.take 2 tx1) tx2

    f :: IsCommerce -> Val管理補助的業務 -> Text -> Text
    f _      Null                               tx     = tx
    f _     (V管理補助的業務 E管理補助的業務)   tx     | T.take 2 tx == T.pack "93" = tx
                                                       | otherwise                  = g tx (T.pack "00")
    f True  (V管理補助的業務 E自家用倉庫    )   tx     = g tx (T.pack "08")
    f False (V管理補助的業務 E自家用倉庫    )   tx     = g tx (T.pack "09")
    f _     (V管理補助的業務 E補助的業務    )   tx     = g tx (T.pack "09")



-- | H事業所別生産物別売上高 のCars を 管理補助的業務に変換する
{-# INLINE convMCinCars #-}
convMCinCars :: IsCommerce -> Val管理補助的業務 -> Cars -> Cars
convMCinCars !bl !e !cs = merge (V.empty, converted)
    where
    ~ converted = V.map (\x -> let !n = name x in x {name = makeManagementClass bl e n}) cs

    part :: Cars -> (Cars, Cars)
    part !cs | V.null   cs      = (V.empty, V.empty)
             | V.length cs == 1 = (cs, V.empty)
             | otherwise        = (l2, r)
        where
        ~ hd = V.head cs
        ~ hdName = name hd
        (~l,~r)  = V.partition (\x -> name x == hdName) cs
        ~l2     = V.singleton $! Car (V.sum (V.map value l)) hdName

    merge :: (Cars, Cars) -> Cars
    merge (!x,!xs)   | V.null xs = x
                     | otherwise =  let (!l,!r) = part xs
                                 in merge (x V.++ l, r)

-----------------------------------------------------------
-- *** 格付け不能の処理
-----------------------------------------------------------
-- | 格付け不能な分類名 CNC : CanNotClassify
type CNCName = Industry


--- *** 農林漁業
------------------------------------------------------------------
f産業格付_特殊な方法_農林漁業 :: Year -> IOCensusRow -> IO ()
f産業格付_特殊な方法_農林漁業 year icr = do
    kind <- readArray icr H調査票の種類
    case kind of
        V調査票の種類 x             | _対象産業 x == E農林漁業    -> ifSuite year icr
                                    | otherwise                     -> return ()
        _                                                           -> return ()

    where
    -- 農林水産業だった場合の処理
    ifSuite :: Year -> IOCensusRow -> IO ()
    ifSuite year icd = do
        !man            <- readArray icd H管理補助的業務
        !comm           <- readArray icd H事業所別生産物別売上高
        !front          <- readArray icd H事業別売上高
        !prod           <- readArray icd H生産_農林漁業_金額

        let behind = getValCarsFromV農林漁業 man prod
        mergeFrontAndBehind icr comm behind front ["T1"]


-- | 単純に生産_農林漁業_金額の項目を事業所別生産物別売上高に振り分ける
getValCarsFromV農林漁業 :: Val管理補助的業務 -> Val生産_農林漁業_金額 -> Val事業所別生産物別売上高
getValCarsFromV農林漁業 man Null       =  Null
getValCarsFromV農林漁業 man (VCars cs) =  VCars
                                         $! convMCinCars False man {-  管理補助的業務の処理 -}
                                         $! cs


-- *** 鉱業
------------------------------------------------------------------
f産業格付_特殊な方法_鉱業 :: Year -> IOCensusRow -> IO ()
f産業格付_特殊な方法_鉱業 year icr = do
    kind <- readArray icr H調査票の種類
    case kind of
        V調査票の種類 x             | _対象産業 x == E鉱業    -> ifSuite year icr
                                    | otherwise               -> return ()
        _                                                     -> return ()

    where
    -- 鉱業だった場合の処理
    ifSuite :: Year -> IOCensusRow -> IO ()
    ifSuite year icr = do
        !man            <- readArray icr H管理補助的業務
        !comm           <- readArray icr H事業所別生産物別売上高
        !front          <- readArray icr H事業別売上高
        !prod           <- readArray icr H生産_鉱業_金額

        let behind = getValCarsFromV鉱業 man prod
        mergeFrontAndBehind icr comm behind front ["T2"]


-- | 単純に生産_鉱業_金額の項目を事業所別生産物別売上高に振り分ける
getValCarsFromV鉱業 :: Val管理補助的業務 -> Val生産_鉱業_金額 -> Val事業所別生産物別売上高
getValCarsFromV鉱業 man Null       =  Null
getValCarsFromV鉱業 man (VCars cs) =  VCars
                                   $! convMCinCars False man {-  管理補助的業務の処理 -}
                                   $! cs


-- *** 製造業
-----------------------------------------------------------
{- |
    在庫品評価調整の後，センサス細分類との対応関係に基づき品目を編纂する．
    製造業における特殊な方法は，「工業統計調査分類関係資料 産業格付の方法」
    において解説されている以下の記述以外に資料を見つけることができなかった．

    上記の方法以外に、原材料、作業工程、機械設備等により、
    産業を決定しているものがある。その産業とは、「中分類22 鉄鋼業」に属する「高炉による製鉄業」、
    「製鋼・製銅圧延業（転炉・電気炉を含む）」、「熱間圧延業」、「冷間圧延業」、「冷間ロール成型形鋼製造業」、
    「鋼管製造業」、「伸鉄業」、「磨棒銅製造業」、「引抜鋼管製造業」、「伸線業」及び「その他の製鋼を行わない鋼材製造業」
    の11 産業である。

    工業統計調査においては原材料，作業工程，機械設備等を用いて産業を把握しているが，
    経済センサスにおける事業所調査票（製造業）における調査項目には「作業工程」及び「主要原材料」が存在し，
    それぞれ自由記述にてその内容を調査しており，これらの情報を用いて，産業の把握が可能であると考えらえる．
    工業統計調査では，例として，形鋼を製造していても，鉄鉱石，石炭，石灰石を原材料，高炉を機械設備としている場合，
    「高炉による製鉄業」に格付けされ，銑鉄，鉄屑を原材料とし，転炉，電気炉を機械設備としている場合には，
    「製鋼・製鋼圧延業」に格付けされるなどの処理が行われている．

    このような分類の組み合わせを全て把握すれば，その再現は可能であると思われるが，
    その詳細が不明であることから，それらの格付けに関してはある程度製造品で候補を選定し，
    案分する等の処理を行うものとする．

    また，製造業においては副産物，特に自家生産・自家消費品にも注意が必要とされる．
    生産過程における中間製品であり，自家生産されたものが全て自家消費される財に関しては産業連関表においては，
    経済センサス等の出荷ベース統計では把握されないため原則として計上されないが，銑鉄と粗鋼など，
    投入・算出構造が異なる場合には，それぞれ支柱の製品価格を基準として国内生産額として計上される．

    したがって，それらの把握には，生産動態統計などの生産高ベースの統計を資料として用いているが，
    経済センサスにおいて把握するためには，投入構造を一定と仮定して，
    原材料使用額等から推測される自家生産・自家消費分を推計する必要がある．
    しかし，それらの投入構造の把握，推計が困難であることから本稿ではこれを扱わず，
    自家生産・自家消費分を除いた産出量として推計する．

    取引基本表では、各部門の生産物について、自主的な生産はもとより、
    他部門からの受託に基づく生産であっても、当該生産物の部門に金額を計上するのが原則である。
    しかし、国内生産額を推計する基礎資料の一つである経済センサス‐活動 調査では、受託生産分に係る金額については、
    「加工賃収入」しか把握されていない。
    そのため、同調査を利用して国内生産額を推計する部門では、 受託生産に係る原材料等の金額が把握できない。

    一方、受託生産の委託者が非製造業の場合にあっては、商社や百貨店などの商業部門である場合が多いが、
    これら商業部門の国内生産額は、基本的に「販売額 - 売上原価 = 商業マージン額」
     (商業部門の国内生産額には、このほか、コスト 商業に相当する金額も含まれる。)で計算されるため、
     委託生産のための材料購入費が発生していたとしても、商業部門には計上されない。

    その結果、何も処理を行わないとすれば、原材料を生産した部門では、
    商業部門に販売した委託生産用原材料の産出を計上できなくなる一方で、
    受託生産を行った部門では、国内生産額が過小評価になるとともに、付加価値率が過大評価になる。

    そこで、非製造業からの委託を受けて生産する 分については、次に掲げる式により、
    加工賃収入額に付加価値率の逆数を乗ずることにより、原材料費等を含んだ国内生産額を推計している。

    \[ 国内生産額 = 加工賃収入額 \times \frac{製品価額}{製品額-原材料費}   \]

    (データの欠損等で付加価値率の逆数が0,マイナス,無限大になる場合は,全て1としている.)


    くず・廃物    7466 00 製造工程からでたくず・廃物

    に関して 製造業の段階で発生部門に振り分け
    また，屑・副産物に関しては，取引基本表における屑・副産物発生部門をV表産業分類へ組替え，その値をセンサスから求められた産業×商品表の当該交点に計上している．

     本稿ではV表の作成は大まかに，以下①~⑤の作業を想定している．
    なお，現行のV表の作成においては，屑，副産物の推計において取引基本表を経由しており，経済センサス以外の各種基礎統計値もその推計に利用している．
     本研究は，飽くまで同一データを利用することで推計手法毎の差異を分析することを目的としており，センサスデータから直接的に値を構成するという点で，
    推計手法が現行のものとは異なる．
    幾つかの補足できない概念等もそのまま未把握として扱い，大きな項目については他の統計を用いて簡易的に推計するなど，簡易的作成手法を採用する．

    -}

f産業格付_特殊な方法_製造業 :: Year -> IOCensusRow -> IO ()
f産業格付_特殊な方法_製造業  year icr = do
    -- 調査票の種類で，処理を行うか判定する
    kind <- readArray icr H調査票の種類
    case kind of
        V調査票の種類 x     | _対象産業 x == E製造業            -> ifSuite year icr
                            | otherwise                         -> return ()
        _                                                       -> return ()

    where
    -- 製造業だった場合の処理
    ifSuite :: Year -> IOCensusRow -> IO ()
    ifSuite year icr = do
        !man            <- readArray icr H管理補助的業務
        !comm           <- readArray icr H事業所別生産物別売上高
        !front          <- readArray icr H事業別売上高
        !prod           <- readArray icr H出荷額_製造業
        !process        <- readArray icr H収入額_加工賃
        !oth            <- readArray icr H収入額_製造業以外
        !cost           <- readArray icr H原材料使用額

        --  軽くするため，使用しない項目に関してはNullにしてもいいかもしれない（要件等）
        -- ここで,以前に処理されていた場合の対処を分岐
        let behind = getValCarsFromV製造業 year man prod process oth cost
        mergeFrontAndBehind icr comm behind front ["T3"]

getValCarsFromV製造業 :: Year
                      -> Val管理補助的業務
                      -> Val出荷額_製造業
                      -> Val収入額_加工賃
                      -> Val収入額_製造業以外
                      -> Val原材料使用額
                      -> Val事業所別生産物別売上高
getValCarsFromV製造業 year man prod process oth  cost = merge prodDetail processDetail othDetail
    where
    -- | 製造業
    ~ prodDetail = prodToDetail year prod
    -- | 加工賃を除く製造額
    ~ totalProd = sumCars prodDetail

    -- | 加工賃
    ~ processDetail = processToDetail cost totalProd process
    -- | 製造業以外
    ~ othDetail = othToDetail oth
    -- | 処理方針 : それぞれ,変換して結合する
    -- | 結合
    merge :: Cars出荷額_製造業 -> Cars収入額_加工賃 -> Cars収入額_製造業以外 -> Val事業所別生産物別売上高
    merge c1 c2 c3 | and (map V.null [c1,c2,c3]) = Null
                   | otherwise                   = VCars $! convMCinCars False man  $! c1 V.++ c2 V.++ c3


-- | 出荷額
-- 出荷額は基本的に,前四文字に切ると,細分類になる
-- ｢くず・廃物    7466 00 製造工程からでたくず・廃物｣ は その事業所の出荷製品の最大のものに変換

prodToDetail :: Year -> Val出荷額_製造業 -> Cars事業所別生産物別売上高
prodToDetail _   Null        = V.empty
prodToDetail 28  (VCars cs)  = let cutted = V.map (\x ->  x { name = ((T.take 4) . name) x } ) cs
                                    in wasteTreate cutted

prodToDetail 24  (VCars cs)  =  let cutted = V.map (\x ->  x { name = ((T.take 4) . name) x } ) cs
                                    in wasteTreate cutted

-- | ｢くず・廃物    7466 00 製造工程からでたくず・廃物｣  を その事業所の出荷製品の最大のものに変換
wasteTreate :: Cars出荷額_製造業 -> Cars事業所別生産物別売上高
wasteTreate cs =  let waste        = V.filter (\x -> name x == T.pack "7466") cs
               in case V.null waste of
                  True  -> cs
                  False -> let withoutWasteMaxValueName = VDS.vmaximumNameWithoutErr (V.filter (\x -> name x /= T.pack "7466") cs)
                        in case T.null withoutWasteMaxValueName of
                            True  -> mergeSameNameCars $! V.map (\x -> Car (value x) (T.pack "EZZZ")) waste
                            False -> mergeSameNameCars $! V.map (\x -> if name x == T.pack "7466" then x { name = withoutWasteMaxValueName} else x ) cs

-- | 賃加工
-- 前四文字で切った後に,賃加工以外の製造品の原材料費
-- 原材料使用額か,製造品価額がわからない場合はそのまま足す
-- 過少になるため,代替案は必要

processToDetail :: Val原材料使用額 -> Double ->  Val収入額_加工賃 -> Cars
processToDetail _    _          Null       = V.empty
processToDetail cost totalProd (VCars cs)  = V.map (\x -> x { value = (getRate cost totalProd) * (value x)
                                                            , name = ((T.take 4) . name) x}) cs
    where
    -- 付加価値率の逆数を求める関数
    getRate :: Val原材料使用額 -> Double {- ^ 総製造額 -} -> Double {- ^ 付加価値の逆数 -}
    getRate Null          _ = 1
    getRate (VDouble d1) d2 | (d2 - d1) <= 0 = 1
                            | otherwise      = d2 / (d2 - d1)


-- | 製造業以外
othToDetail :: Val収入額_製造業以外 -> Cars
othToDetail Null        = V.empty
othToDetail (VCars cs ) = lookupCarsNameErr cs gd製造業以外


-- *** 商業
-----------------------------------------------------------

{- |
    平成24年経済センサスにおける事業所調査票（卸売業，小売業）がどのように格付けされているかに関する情報は，
    筆者の知る限り公表されていないが，平成28年結果の概要において，商業における産業格付けの「特殊な方法」に関して詳細な記述が存在する．

    在庫に関する調査項目以外には，平成24年経済センサス及び平成28年経済センサスにおける商業部門の調査票の設計に大きな違いはないため，
    ここでは，平成28年「結果の概要」に記述されている手法に則って，産業格付けを行う．

    同資料によれば，『卸売業，小売業の産業格付けにおいて，卸売業のうち「各種商品卸売業（従業者が常時100人以上のもの）」，
    「その他の各種商品卸売業」及び「代理商，仲立業」，小売業のうち「百貨店，総合スーパー」，
    「その他の各種小売業（従業員が常時50人未満のもの）」，「各種食料品小売業」，
    「コンビニエンスストア（新食料品を中心とするものに限る）」，
    「ドラッグストア」，「ホームセンター」，「たばこ・喫煙具専門小売業」及び「無店舗小売業」』は特殊な方法によって格付けされている．

    結果の概要に記載されている処理フローをまとめたものが，「図 6商業における特殊な方法のワークフロー図」である．
    以下，ワークフローに従って処理を設計していく

    ![商業における特殊な方法のワークフロー図](commerceFlow.png)

    類似マージン率取得 などの処理は，他の処理が終了した後に処理される．


    * 商業は,商品分類=産業分類細分類になっているので,変換の必要なし.
-}

f産業格付_特殊な方法_商業 :: Year -> IOCensusRow -> IO ()
f産業格付_特殊な方法_商業 year icr = do
    -- 調査票の種類で，処理を行うか判定する
    kind <- readArray icr H調査票の種類
    case kind of
        V調査票の種類 x     | _対象産業 x == E商業              -> ifSuite year icr
                            | otherwise                         -> return ()
        _                                                       -> return ()

    where
    -- | 商業だった場合の処理
    ifSuite :: Year -> IOCensusRow  -> IO ()
    ifSuite year icr = do
        !man            <- readArray icr H管理補助的業務
        !comm           <- readArray icr H事業所別生産物別売上高
        !front          <- readArray icr H事業別売上高
        !retail         <- readArray icr H商品別小売額
        !wholesale      <- readArray icr H商品別卸売額
        !area           <- readArray icr H売場面積
        !self           <- readArray icr Hセルフサービス
        !sellType       <- readArray icr H販売形態
        !goodsType      <- readArray icr H商品形態
        !shopType       <- readArray icr H店舗形態_商業
        !repair         <- readArray icr H修理手数料収入_商業
        !middle         <- readArray icr H仲立手数料収入_商業
        !open           <- readArray icr H開店閉店期間
        !worker         <- readArray icr H雇用情報


        -- 軽くするため，使用しない項目に関してはNullにしてもいいかもしれない（要件等）
        -- ここで,以前に処理されていた場合の対処を分岐
        let behind = getValCarsFromV商業 year man front retail wholesale repair middle area self sellType goodsType shopType open worker
        mergeFrontAndBehind icr comm behind front ["T4", "T5"]

getValCarsFromV商業 :: Year
                    -> Val管理補助的業務
                    -> Val事業別売上高
                    -> Val商品別小売額
                    -> Val商品別卸売額
                    -> Val修理手数料収入_商業
                    -> Val仲立手数料収入_商業
                    -> Val売場面積
                    -> Valセルフサービス
                    -> Val販売形態
                    -> Val商品形態
                    -> Val店舗形態_商業
                    -> Val開店閉店期間
                    -> Val雇用情報
                    -> ValCars
getValCarsFromV商業 year man seb retail wholesale repair middle area self sellType goodsType shopType open worker
    = case (retail == Null, wholesale == Null ) of
        (True, False)   -> f産業分類変換CNC year $! f小売処理 retail sellType area self open shopType worker
        (False, True)   -> f産業分類変換CNC year $! f卸売処理 middle wholesale worker
        (True,  True)   -> f (f産業分類変換CNC year (f小売処理 retail sellType area self open shopType worker))
                             (f産業分類変換CNC year (f卸売処理 middle wholesale worker))
        (False, False)  -> Null

    where
    f Null        Null        = Null
    f (VCars xs)  Null        = (VCars xs)
    f Null        (VCars ys)  = (VCars ys)
    f (VCars xs)  (VCars ys)  = VCars $! (V.++) xs ys


    -- | CNCの対応をしたあとに,産業分類へ振り返る
    f産業分類変換CNC :: Year -> ValCars -> ValCars
    f産業分類変換CNC _  Null        =  Null
    f産業分類変換CNC 24 (VCars cs)  =  VCars $! convMCinCars True man cs
    f産業分類変換CNC 28 (VCars cs)  =  VCars $! convMCinCars True man cs


-- **** 小売業
------------------------------------------------------------------
{- |    小売業の処理

        * 喫煙具処理
        「6092 たばこ・喫煙具専門小売業」

        商品分類番号「6092」（たばこ・喫煙具専門小売業に属する品目）の販売額が小売販売総額の
        90％以上の事業所

        喫煙具に関しては,自動的に,一般的な方法で処理されるのでなにもしない.

-}

f小売処理 ::Val商品別小売額
            -> Val販売形態
            -> Val売場面積
            -> Valセルフサービス
            -> Val開店閉店期間
            -> Val店舗形態_商業
            -> Val雇用情報
            -> Val事業所別生産物別売上高
f小売処理 retail sellType area self open shopType worker
    | more50従業員 worker = fその他の各種商品小売業処理 retail sellType area
    | otherwise           = f百貨店処理 retail sellType area self open shopType

-- | 従業員数が50以上か判定する
more50従業員 :: Val雇用情報 -> Bool
more50従業員 Null = False
more50従業員 (V雇用情報 em) | _企事業従業者数 em >= 50 || _事事業従業者数 em >= 50 = True
                            | otherwise                                            = False

{- |ア 「5611 百貨店，総合スーパー」

    表3の「衣」、「食」及び「他」にわたる商品を小売りし、「衣」、「食」及び「他」の各販売
    額がいずれも小売販売総額の10％以上70％未満で、従業者が50人以上の事業所

    * 表3 「衣」、「食」及び「他」と商品分類

    衣・食・他別 商品分類番号上位2桁 以下の産業分類に属する品目

    > 衣 57 織物・衣服・身の回り品小売業
    > 食 58 飲食料品小売業
    > 他 59 機械器具小売業
    > 他 60 その他の小売業

    -}
f百貨店処理 :: Val商品別小売額
            -> Val販売形態
            -> Val売場面積
            -> Valセルフサービス
            -> Val開店閉店期間
            -> Val店舗形態_商業
            -> ValCars
f百貨店処理 retail sellType area self open shopType
    | more10Less70Every表3 retail    =  VCars
                                    $! V.singleton
                                    $! Car (sumValCars retail) (T.pack "5699")
    | otherwise
        = case f小売中小分類格付 retail of
            Nothing -> Null
            Just (middle,small)
                    | middle == T.pack "60"  -> fその他の各種商品小売業処理 retail sellType area
                    | middle == T.pack "58"  -> f飲食料品小売処理           retail sellType area self open
                    | small  == T.pack "603" -> fドラッグストア処理         retail sellType area self shopType
                    | otherwise               -> f無店舗処理                retail sellType area



-- | 「衣」、「食」及び「他」の各販売
-- 額がいずれも小売販売総額の10％以上70％未満の判断
more10Less70Every表3 :: Val商品別小売額 -> Bool
more10Less70Every表3 Null        = False
more10Less70Every表3 (VCars cs )
    = runST $ do
        cloth <- newSTRef 0 :: ST s (STRef s Double)
        food  <- newSTRef 0 :: ST s (STRef s Double)
        other <- newSTRef 0 :: ST s (STRef s Double)

        V.forM cs $ classify cloth food other

        allC <- mapM readSTRef [cloth, food, other]
        let more3Kind = 3 <= (L.length (L.filter (0 /=) allC))
        let more10Less70P   =  let total = sumCars cs
                      in L.and (L.map (\x ->  total * 0.1 <= x && total * 0.7 > x  ) allC)
        return $ more3Kind && more10Less70P

    where
    ------------------------------------------------------------------
    classify :: (STRef s Double) -> (STRef s Double) -> (STRef s Double)
             -> Car -> ST s ()
    classify cloth food other ca
        | n == T.pack "57"                         = modifySTRef cloth (\x -> x + value ca)
        | n == T.pack "58"                         = modifySTRef food  (\x -> x + value ca)
        | n == T.pack "59"  || n == T.pack "60"    = modifySTRef other (\x -> x + value ca)
        | otherwise                                = return ()
        where ~ n = T.take 3 (name ca)



{- | イ 「5699 その他の各種商品小売業（従業者が常時50人未満のもの）」

表3の「衣」、「食」及び「他」にわたる商品を小売りし、「衣」、「食」及び「他」の各販売
額がいずれも小売販売総額の50％未満で、従業者が50人未満の事業所

-}

fその他の各種商品小売業処理 :: Val商品別小売額 -> Val販売形態 -> Val売場面積 -> ValCars
fその他の各種商品小売業処理 retail sellType area
    | less50Every表3 retail  =  VCars
                             $! V.singleton
                             $! Car (sumValCars retail) (T.pack "5699")
    | otherwise              = f無店舗処理 retail sellType  area

less50Every表3 :: Val商品別小売額 -> Bool
less50Every表3 Null        = False
less50Every表3 (VCars cs )
    = runST $ do
        cloth <- newSTRef 0 :: ST s (STRef s Double)
        food  <- newSTRef 0 :: ST s (STRef s Double)
        other <- newSTRef 0 :: ST s (STRef s Double)

        V.forM cs $ classify cloth food other

        allC <- mapM readSTRef [cloth, food, other]
        let more3Kind = 3 <= (L.length (L.filter (0 /=) allC))
        let less50P   = L.and (L.map ( (sumCars cs) * 0.5 <= ) allC)
        return $ more3Kind && less50P

    where
    ------------------------------------------------------------------
    classify :: (STRef s Double) -> (STRef s Double) -> (STRef s Double)
             -> Car -> ST s ()
    classify cloth food other ca
        | n == T.pack "57"                         = modifySTRef cloth (\x -> x + value ca)
        | n == T.pack "58"                         = modifySTRef food  (\x -> x + value ca)
        | n == T.pack "59"  || n == T.pack "60"    = modifySTRef other (\x -> x + value ca)
        | otherwise                                = return ()
        where ~n = T.take 3 (name ca)

{- | 以下の,処理のために,中分類,小分類で一旦格付けを行う.

格付け不能の場合は,Nothing を返す
-}

f小売中小分類格付 :: Val商品別小売額 -> Maybe (Text, Text)
f小売中小分類格付 Null        = Nothing
f小売中小分類格付 (VCars cs)  = Just (middle, small)
    where
    ~small   = VDS.vmaximumNameWithoutErr
            $! mergeSameNameCars
            $! V.map (\x -> x {name = T.take 3 (name x)}) cs
    ~middle  = VDS.vmaximumNameWithoutErr
            $! mergeSameNameCars
            $! V.map (\x -> x {name = T.take 2 (name x)}) cs




{- | ドラッグストアの処理
    * オ 「6031 ドラッグストア」

    小分類「603 医薬品・化粧品小売業」に格付けされた事業所のうち、以下のいずれかの事業所

    ・ セルフサービス方式を採用しており、｢6032 一般用医薬品｣ を小売りしている事業所

    ・ セルフサービス方式を採用しており、「店舗形態」において「ドラッグストア」を選択した事業所
-}

fドラッグストア処理 :: Val商品別小売額
                    -> Val販売形態
                    -> Val売場面積
                    -> Valセルフサービス
                    -> Val店舗形態_商業
                    -> ValCars
fドラッグストア処理 retail sellType area self shopType
    | (isセルフ self) &&  (isドラッグストア shopType) = VCars $! V.singleton $! Car (sumValCars retail) "6031"
    | (isセルフ self) &&  (include retail)            = VCars $! V.singleton $! Car (sumValCars retail) "6031"
    | otherwise                                       = f無店舗処理 retail sellType  area
    where
    isドラッグストア :: Val店舗形態_商業 -> Bool
    isドラッグストア Null                                        = False
    isドラッグストア (V店舗形態_商業 sk) | sk == Eドラッグストア = True
                                         | otherwise             = False
    ------------------------------------------------------------------
    included :: Val商品別小売額 -> Bool
    included Null       = False
    include (VCars cs)  =  0 <= len
                        where ~len   = V.length
                                    $ (flip V.filter) cs
                                    $ \x -> name x == "6032"


{- | 中分類「58 飲食料品小売業」のときの処理

    *「5891 コンビニエンスストア（飲食料品を中心とするものに限る）」

    中分類「58 飲食料品小売業」に格付けされた事業所のうち、セルフサービス方式を採用し、売
    場面積が30㎡以上250㎡未満で、営業時間が14時間以上の事業所

    *「5811 各種食料品小売業」

    中分類「58 飲食料品小売業」に格付けされた事業所のうち、表4の商品分類番号上位3桁で分類
    集計した小売販売額が3つ以上あり、そのいずれもが商品分類番号「58」（飲食料品小売業に属す
    る品目）の総額の50％に満たない事業所


    *表4 飲食料品小売業と商品分類

    産業分類 商品分類番号

    上位3桁 以下の産業分類に属する品目

    > 58 飲食料品小売業
    > 582 野菜・果実小売業
    > 583 食肉小売業
    > 584 鮮魚小売業
    > 585 酒小売業
    > 586 菓子・パン小売業
    > 589 その他の飲食料品小売業
-}

f飲食料品小売処理   :: Val商品別小売額
                    -> Val販売形態
                    -> Val売場面積
                    -> Valセルフサービス
                    -> Val開店閉店期間
                    -> ValCars
f飲食料品小売処理 retail sellType area self open
    | (isセルフ self) && (more30Less250 area) && (more14hour open)  =  VCars
                                                                    $! V.singleton
                                                                    $! Car (sumValCars retail) "6091"

    | less50Every表4 retail                                         =  VCars
                                                                    $! V.singleton
                                                                    $! Car (sumValCars retail) "5811"

    | otherwise                                                     = f無店舗処理 retail sellType  area

    where
    --  | 売場面積が30㎡以上250㎡未満 の判定
    more30Less250 :: Val売場面積 -> Bool
    more30Less250 Null          = False
    more30Less250 (VDouble dl)  | dl >= 30 && 250 > dl = True
                                | otherwise            = False
    -- | 営業時間が14時間以上の判定
    more14hour :: ValInt -> Bool
    more14hour Null         = False
    more14hour (VInt num)   | num >= 14 = True
                            | otherwise = False

-- | 中分類「58 飲食料品小売業」に格付けされた事業所のうち、表4の商品分類番号上位3桁で分類
--   集計した小売販売額が3つ以上あり、そのいずれもが商品分類番号「58」（飲食料品小売業に属す
--   る品目）の総額の50％に満たない事業所の判定

less50Every表4 :: Val商品別小売額 -> Bool
less50Every表4 Null        = False
less50Every表4 (VCars cs )
    = runST $ do
        c582 <- newSTRef 0 :: ST s (STRef s Double)
        c583 <- newSTRef 0 :: ST s (STRef s Double)
        c584 <- newSTRef 0 :: ST s (STRef s Double)
        c585 <- newSTRef 0 :: ST s (STRef s Double)
        c586 <- newSTRef 0 :: ST s (STRef s Double)
        c589 <- newSTRef 0 :: ST s (STRef s Double)

        V.forM cs $ classify c582 c583 c584 c585 c586 c589

        allC <- mapM readSTRef [c582, c583, c584, c585, c586, c589]
        let more3Kind = 3 <= (L.length (L.filter (0 /=) allC))
        let less50P   = L.and (L.map (totalTop58 * 0.5 <= ) allC)
        return $ more3Kind && less50P
    where
    ~totalTop58 = sumCars
                $! (flip V.filter) cs
                $ \x -> T.take 2 (name x) == T.pack "58"
    ------------------------------------------------------------------
    classify :: (STRef s Double) -> (STRef s Double) -> (STRef s Double)
             -> (STRef s Double) -> (STRef s Double) -> (STRef s Double)
             -> Car -> ST s ()
    classify c582 c583 c584 c585 c586 c589 ca
        | n == T.pack "582" = modifySTRef c582 (\x -> x + value ca)
        | n == T.pack "583" = modifySTRef c583 (\x -> x + value ca)
        | n == T.pack "584" = modifySTRef c584 (\x -> x + value ca)
        | n == T.pack "585" = modifySTRef c585 (\x -> x + value ca)
        | n == T.pack "586" = modifySTRef c586 (\x -> x + value ca)
        | n == T.pack "589" = modifySTRef c589 (\x -> x + value ca)
        | otherwise                             = return ()
        where ~n = T.take 3 (name ca)

{- | ホームセンター処理
    中分類「60 その他の小売業」に格付けされた事業所のうち、以下のいずれかの事業所

    ・ セルフサービス方式を採用し、売場面積が500㎡以上で、金物、荒物、苗・種子のいずれかを小売りしている事業所

    ・ セルフサービス方式を採用し、売場面積が500㎡以上で、「店舗形態」において「ホームセンター」を選択した事業所

    > 6021    金物小売業
    > 6022    荒物小売業
    > 6042    苗・種子小売業
    > 6091    ホームセンター-}

fホームセンター処理 :: Valセルフサービス
                    -> Val売場面積
                    -> Val店舗形態_商業
                    -> Val商品別小売額
                    -> Val販売形態
                    -> ValCars
fホームセンター処理 self area shopType retail sellType
    | tempBool  = VCars $! V.singleton $! Car (sumCars (cars retail)) (T.pack "6091")
    | otherwise = f無店舗処理 retail sellType  area
    where
    ~tempBool = (isセルフ self) && (more500 area) && (isホームセンター shopType || inclued retail)
    ------------------------------------------------------------------
    isホームセンター :: Val店舗形態_商業 -> Bool
    isホームセンター Null = False
    isホームセンター (V店舗形態_商業 sk) | sk == Eホームセンター = True
                                         | otherwise             = False
    ------------------------------------------------------------------
    more500 :: Val売場面積 -> Bool
    more500 Null         = False
    more500 (VDouble dl) | dl >=  500 = True
                         | otherwise  = False
    ------------------------------------------------------------------
    inclued :: Val商品別小売額 -> Bool
    inclued Null       = False
    inclued (VCars cs) =  let names = V.toList (V.map name cs)
                       in L.or $ L.map (\x -> L.elem x names)
                       $ L.map T.pack ["6021","6022","6042"]


-- | セルフサービスか否かの判定
isセルフ :: Valセルフサービス -> Bool
isセルフ Null = False
isセルフ (VBool bl) = bl


{- | 無店舗処理
    * 「61 無店舗小売業」
    販売形態の店頭販売の割合が0％及び売場面積が0㎡の事業所

    自動販売機,その他に関しては,そのままCarに追加する

    6121    自動販売機による小売業

    6199    その他の無店舗小売業

    無店舗でないものは調査品目名 = 産業細分類なのでそのまま用いる

    -}

f無店舗処理 :: Val商品別小売額 ->  Val販売形態 -> Val売場面積 -> ValCars
f無店舗処理 Null   Null      Null =  Null
f無店舗処理 retail sellType  area =
    case is無店舗 sellType area of
            False   | sellType == Null -> retail
                    | otherwise        -> appendVCars outAndOth retail

            True    | sellType == Null ->                         f無店舗小売振替 retail
                    | otherwise        -> appendVCars outAndOth $ f無店舗小売振替 retail

    where
    ~outo  = Car ((_自動販売機 . _販売形態) sellType) (T.pack "6121")
    ~oth   = Car ((_その他販売 . _販売形態) sellType) (T.pack "6199")
    ~outAndOth = V.fromList [outo, oth]

    f無店舗小売振替 :: Val商品別小売額 -> ValCars
    f無店舗小売振替 Null        = Null
    f無店舗小売振替 (VCars cs)  = VCars $! lookupCarsNameErr cs dd無店舗小売業

    --  | 無店舗か否かの判断
    is無店舗 :: Val販売形態 -> Val売場面積 -> Bool
    is無店舗 Null                Null          = False
    is無店舗 (V販売形態 sell)    _             | _店頭販売 sell == 0 = True
                                               | otherwise           = False
    is無店舗 _                  (VDouble dl)   | dl == 0             = True
                                               | otherwise           = False



-- **** 卸売業
------------------------------------------------------------------
{- | 卸売業の処理
    * ウ 「5598 代理商，仲立業」

    卸売の商品販売額（仲立手数料を除く。）と仲立手数料を比較し、仲立手数料が多い場合に「代
理商，仲立業」に格付けする。
-}
f卸売処理 :: Val仲立手数料収入_商業 -> Val商品別卸売額 ->  Val雇用情報 -> ValCars
f卸売処理 Null   Null      Null     = Null
f卸売処理 middle wholesale worker
    | canBe各種商品卸売業 wholesale = VDS.appendVCars mid $! f卸売処理2 wholesale worker
    | otherwise                     = VDS.appendVCars mid $! VCars mid
    where ~mid = make代理商 middle



{- |
    * 「5011 各種商品卸売業（従業者が常時100人以上のもの）」
    表2の財別（生産財、資本財及び消費財）の3財にわたる商品を卸売りし、各財の販売額がいずれ
    も卸売販売総額（仲立手数料を除く。）の10％以上で、従業者が100人以上の事業所

    * 「5019 その他の各種商品卸売業」
    表2の財別（生産財、資本財及び消費財）の3財にわたる商品を卸売りし、商品分類番号上位3桁
    の販売額で分類集計した販売額がいずれも卸売販売総額（仲立手数料を除く。）の50％未満で、従
    業者が100人未満の事業所

    * 表2 財別と商品分類

    +--------+--------------------+-----+
    | 商品分類番号 | 以下の産業分類に属する品目      | 財別  |
    |   上位3桁 |                    |     |
    +========+====================+=====+
    | 511    | 繊維品卸売業（衣服，身の回り品を除く）| 生産財 |
    +--------+--------------------+     |
    | 532    | 化学製品卸売業            |     |
    +--------+--------------------+     |
    | 533    | 石油・鉱物卸売業           |     |
    +--------+--------------------+     |
    | 534    | 鉄鋼製品卸売業            |     |
    +--------+--------------------+     |
    | 535    | 非鉄金属卸売業            |     |
    +--------+--------------------+     |
    | 536    | 再生資源卸売業            |     |
    +--------+--------------------+-----+
    | 531    | 建築材料卸売業            | 資本財 |
    +--------+--------------------+     |
    | 541    | 産業機械器具卸売業          |     |
    +--------+--------------------+     |
    | 542    | 自動車卸売業             |     |
    +--------+--------------------+     |
    | 543    | 電気機械器具卸売業          |     |
    +--------+--------------------+     |
    | 549    | その他の機械器具卸売業        |     |
    +--------+--------------------+-----+
    | 512    | 衣服卸売業              | 消費財 |
    +--------+--------------------+     |
    | 513    | 身の回り品卸売業           |     |
    +--------+--------------------+     |
    | 521    | 農畜産物・水産物卸売業        |     |
    +--------+--------------------+     |
    | 522    | 食料・飲料卸売業           |     |
    +--------+--------------------+     |
    | 551    | 家具・建具・じゅう器等卸売業     |     |
    +--------+--------------------+     |
    | 552    | 医薬品・化粧品等卸売業        |     |
    +--------+--------------------+     |
    | 553    | 紙・紙製品卸売業           |     |
    +--------+--------------------+     |
    | 559    | 他に分類されない卸売業        |     |
    +--------+--------------------+-----+


    なお、上記ア、イについて、生産財、資本財及び消費財の3財にわたる商品を扱っていても、生産
    財の商品分類番号が「536」（再生資源卸売業に属する品目）のみ、または、消費財の商品分類番号
    が「559」（他に分類されない卸売業に属する品目）のみの場合には、一般的な方法による卸売業格
    付けとする。
-}

f卸売処理2 :: Val商品別卸売額 ->  Val雇用情報 -> ValCars
f卸売処理2 Null      _         = Null
f卸売処理2 wholesale worker
    = case more100従業員 worker of
        False | less50Every3財 wholesale -> VCars
                                         $! V.singleton
                                         $! Car (sumValCars wholesale) (T.pack "5019")
              | otherwise                -> wholesale

        True  | more10Every3財 wholesale -> VCars
                                         $! V.singleton
                                         $! Car (sumValCars wholesale) (T.pack "5011")
              | otherwise                -> wholesale


-- | 代理商の処理
-- 判定しなくても勝手に,一般的な方法で代理商になるので,作る
make代理商 :: Val仲立手数料収入_商業 -> Cars
make代理商 Null          = V.empty
make代理商 (VDouble dl)  = V.singleton $ Car dl (T.pack "5598")

{- | 生産財、資本財及び消費財の3財にわたる商品を扱っているか判定

    生産財の商品分類番号が「536」（再生資源卸売業に属する品目）のみ、または、消費財の商品分類番号
    が「559」（他に分類されない卸売業に属する品目）のみの場合には、一般的な方法による卸売業格
    付けとする。

生産財,資本財,消費財それぞれを素数に変換し,その積に対して,最小公倍数のあまりをとって0なら,3財全て含まれると言う判定.
-}
canBe各種商品卸売業 :: Val商品別卸売額 -> Bool
canBe各種商品卸売業 Null        = False
canBe各種商品卸売業 (VCars cs)
    =  let cs2 = V.filter (\x -> (T.take 3 (name x)) /= T.pack "536" && (T.take 3 (name x)) /= T.pack "559") cs
    in (==) 0
    $ (flip mod) 30
    $ V.foldl1 (*)
    $ (flip V.map) cs2
    $  \ c -> case Map.lookup (T.take 3 (name c)) VDC.ge卸売財別商品 of
                Nothing -> 1
                Just ez | ez == E生産財 -> 2
                        | ez == E資本財 -> 3
                        | ez == E消費財 -> 5

-- | 従業員(事業従業者数)が100人以上か判定する
more100従業員 :: Val雇用情報 -> Bool
more100従業員 Null = False
more100従業員 (V雇用情報 em) | _企事業従業者数 em >= 100 || _事事業従業者数 em >= 100 = True
                             | otherwise                                              = False


-- | 3財がそれぞれ総額の10%以上か判定する
more10Every3財 :: Val商品別卸売額 -> Bool
more10Every3財 Null        = False
more10Every3財 (VCars cs ) = runST $ do
                         let total = sumCars cs
                         inp <- newSTRef 0 :: ST s (STRef s Double)
                         cap <- newSTRef 0 :: ST s (STRef s Double)
                         con <- newSTRef 0 :: ST s (STRef s Double)
                         V.forM_ cs $ \c ->
                            case Map.lookup (T.take 3 (name c)) VDC.ge卸売財別商品 of
                                Nothing -> return ()
                                Just ez  | ez == E生産財 -> modifySTRef inp (\x -> x + (value c))
                                         | ez == E資本財 -> modifySTRef inp (\x -> x + (value c))
                                         | ez == E消費財 -> modifySTRef inp (\x -> x + (value c))
                         inp' <- readSTRef inp
                         cap' <- readSTRef cap
                         con' <- readSTRef con
                         return $! L.and $! L.map (total * 0.1 <= ) [inp', cap', con']


-- | 3財がそれぞれ総額の50%以下か判定する
-- 24年は28年より商品分類の桁数が一つ大きいので,三桁に変換して,同様の処理を行う.
less50Every3財 :: Val商品別卸売額 -> Bool
less50Every3財 Null        = False
less50Every3財 (VCars cs ) = runST $ do
                         let total = sumCars cs
                         inp <- newSTRef 0 :: ST s (STRef s Double)
                         cap <- newSTRef 0 :: ST s (STRef s Double)
                         con <- newSTRef 0 :: ST s (STRef s Double)
                         V.forM_ cs $ \c ->
                            case Map.lookup (T.take 3 (name c)) VDC.ge卸売財別商品 of
                                Nothing -> return ()
                                Just ez  | ez == E生産財 -> modifySTRef inp (\x -> x + (value c))
                                         | ez == E資本財 -> modifySTRef inp (\x -> x + (value c))
                                         | ez == E消費財 -> modifySTRef inp (\x -> x + (value c))
                         inp' <- readSTRef inp
                         cap' <- readSTRef cap
                         con' <- readSTRef con
                         return $! L.and $! L.map (total * 0.5 >= ) [inp', cap', con']



-- *** 医療，福祉
-----------------------------------------------------------
{- |
    医療，福祉産業の産業格付けは平成24年事業所調査票，単独事業所調査票における調査項目「医療，福祉事業の収入の内訳」，
    「事業所の形態，主な事業の内容」を用いる。

    なお，平成28年経済センサスにおいても調査票の構成に大きな変更はないことから，以下同一の処理を想定して論じる。
    また，各調査票の判別には「調査票の種類」を用いる。

    「医療，福祉事業の収入の内訳」においては，7区分された診療及び事業の売上（収入）金額又は割合を調査しており，

    「事業所の形態，主な事業の内容」では,センサス細分類と対応する32区分の事業内容から一つを選択する。

    以下この節に限り，前者を「７区分」，後者を「32区分」と呼称する。

    それぞれ，データとしては,
    * 7区分 E事業収入_医療福祉
    * 32区分 E事業所形態_医療福祉

    に対応する．


    経済センサスにおける産業格付けでは，単純に「事業所の形態，主な事業の内容」を格付けに用いていると考えられる。

    ここでは主生産物及び副生産物の生産量を把握するため,ここでは事業所の形態，主な事業の内容」において選択された事業に，
    「医療，福祉事業の収入の内訳」を配分し，「一般的な方法」を経て，「事業所の形態，主な事業の内容」
    において選択された産業に産業格付けされるようデータを変換する。

    この配分作業に当たって注意すべき事項は，保険区分と産業格付けの対応関係である。
    平成23年（2011年）産業連関表総合解説編 では，
    「医療（入院診療），医療（入院外診療），医療（歯科診療），医療（調剤） ，医療（その他の医療サービス），医療（その他の医療サービス），
    社会福祉（非営利），社会福祉（産業）」において，
    「病院及び一般診療所内での歯科診療は「医療（歯科診療）」に含める」，「介護保険によるサービスは「介護（施設サービス）」，
    「介護（施設サービスを除く）」に含める」と記載されており，歯科とそれ以外はアクティビティで，介護と医療は保険制度で区分がされている。

    以下，基本的にこの区分に従って以下の手法で按分を行う。

    7区分の売上をそれぞれに該当する32区分に案分する第一段階として，32区分それぞれに関してその売上の対象となりうる7区分の対応関係を策定し，
    選択された32区分に,対応のある7区分の収入を全額計上こととする。
    なお,対応関係は「表 1医療,福祉分野における産業区分と事業区分の対応」に従う。
    対応関係のないものに関しては，7区分からなる部門分類を一時的に作成し，そこに全額計上する。
    その後，各32区分の売上の比率で，一時的に計上された7区分を32区分に按分する。
-}

f産業格付_特殊な方法_医療福祉 :: IOCensusRow -> IO ()
f産業格付_特殊な方法_医療福祉 icr =  do
    -- 調査票の種類で，処理を行うか判定する
    kind <- readArray icr H調査票の種類
    case kind of
        V調査票の種類 x     | _対象産業 x ==  E医療福祉 -> ifSuite icr
                            | otherwise                 -> return ()
        _                                               -> return ()

    where
    -- | 医療福祉だった場合の処理
    ifSuite :: IOCensusRow -> IO ()
    ifSuite icr = do
        !man    <- readArray icr H管理補助的業務
        !front  <- readArray icr H事業別売上高
        !comm   <- readArray icr H事業所別生産物別売上高
        !e1     <- readArray icr H事業所形態_医療福祉
        !e2     <- readArray icr H事業収入_医療福祉
        let behind = getValCarsFromV事業所形態_医療福祉 man e1 e2
        mergeFrontAndBehind icr comm behind front ["T22"]


-- | 事業収入_医療福祉 と 事業所形態_医療福祉 の対応関係に基づいてCarを返す．
--
--   V事業所形態_医療福祉 == Null の場合は，格付け不能 "PZZZ" を返す．
getValCarsFromV事業所形態_医療福祉 ::  Val管理補助的業務 ->  Val事業所形態_医療福祉 ->  Val事業収入_医療福祉 -> Val事業所別生産物別売上高
getValCarsFromV事業所形態_医療福祉 man Null Null =  Null
getValCarsFromV事業所形態_医療福祉 man e1   e2   =  VCars
                                                 $! convMCinCars False man {- 管理補助的業務の処理 -}
                                                 $! V.singleton
                                                 $! Car v
                                                 $! getName e1
    where
    ~v = getIncomeE事業収入_医療福祉 e2 e1
    getName :: Val事業所形態_医療福祉 -> Text
    getName Null = T.pack "PZZZ" -- 格付け不可
    getName x    = case Map.lookup (_事業所形態_医療福祉 x) edE事業所形態_医療福祉 of
                 Just n  -> n
                 Nothing -> error "can Not find in edE事業所形態_医療福祉"


-- | E事業所形態_医療福祉 に対応する E事業収入_医療福祉 のフィールド名（関数）を返す
getIncomeE事業収入_医療福祉 :: Val事業収入_医療福祉 -> Val事業所形態_医療福祉 -> Double
getIncomeE事業収入_医療福祉 = f
    where
    g :: Val事業収入_医療福祉 -> [(E事業収入_医療福祉 -> Double)] -> Double
    g e2 = L.sum . (L.map (\func -> func (_事業収入_医療福祉 e2)))
    f Null _                                                        = 0
    f e2 (V事業所形態_医療福祉 E一般病院                          ) = g e2 [ _保険診療収入, _保険外診療収入]
    f e2 (V事業所形態_医療福祉 E精神科病院                        ) = g e2 [ _保険診療収入, _保険外診療収入]
    f e2 (V事業所形態_医療福祉 E有床診療所                        ) = g e2 [ _保険診療収入, _保険外診療収入]
    f e2 (V事業所形態_医療福祉 E無床診療所                        ) = g e2 [ _保険診療収入, _保険外診療収入]
    f e2 (V事業所形態_医療福祉 E歯科診療所                        ) = g e2 [ _保険診療収入, _保険外診療収入]
    f e2 (V事業所形態_医療福祉 E助産所助産師業                    ) = g e2 [ _保険診療収入, _保険外診療収入]
    f e2 (V事業所形態_医療福祉 E看護業                            ) = g e2 [ _保険診療収入, _保険外診療収入]
    f e2 (V事業所形態_医療福祉 E施術業                            ) = g e2 [ _保険診療収入, _保険外診療収入]
    f e2 (V事業所形態_医療福祉 Eその他の療養所                    ) = g e2 [ _保険診療収入, _保険外診療収入]
    f e2 (V事業所形態_医療福祉 E歯科技工所                        ) = g e2 [ _保険診療収入, _保険外診療収入]
    f e2 (V事業所形態_医療福祉 Eその他の医療に附帯するサービス業  ) = g e2 [ _保険診療収入, _保険外診療収入]
    f e2 (V事業所形態_医療福祉 E結核健康相談施設                  ) = g e2 [ _保健衛生事業収入]
    f e2 (V事業所形態_医療福祉 E精神保健相談施設                  ) = g e2 [ _保健衛生事業収入]
    f e2 (V事業所形態_医療福祉 E母子健康相談施設                  ) = g e2 [ _保健衛生事業収入]
    f e2 (V事業所形態_医療福祉 Eその他の健康相談施設              ) = g e2 [ _保健衛生事業収入]
    f e2 (V事業所形態_医療福祉 E検査業                            ) = g e2 [ _保健衛生事業収入]
    f e2 (V事業所形態_医療福祉 E消毒業                            ) = g e2 [ _保健衛生事業収入]
    f e2 (V事業所形態_医療福祉 Eその他の保健衛生                  ) = g e2 [ _保健衛生事業収入]
    f e2 (V事業所形態_医療福祉 E社会保険事業団体                  ) = g e2 [ _社会福祉事業収入]
    f e2 (V事業所形態_医療福祉 E保育所                            ) = g e2 [ _社会福祉事業収入]
    f e2 (V事業所形態_医療福祉 Eその他の児童福祉事業              ) = g e2 [ _社会福祉事業収入]
    f e2 (V事業所形態_医療福祉 E特別養護老人ホーム                ) = g e2 [ _施設介護収入]
    f e2 (V事業所形態_医療福祉 E介護老人保健施設                  ) = g e2 [ _施設介護収入]
    f e2 (V事業所形態_医療福祉 E通所短期入所介護事業              ) = g e2 [ _通所介護訪問介護収入]
    f e2 (V事業所形態_医療福祉 E訪問介護事業                      ) = g e2 [ _通所介護訪問介護収入]
    f e2 (V事業所形態_医療福祉 E認知症老人グループホーム          ) = g e2 [ _施設介護収入]
    f e2 (V事業所形態_医療福祉 Eその他の老人福祉介護事業          ) = g e2 [ _施設介護収入]
    f e2 (V事業所形態_医療福祉 E居住支援事業                      ) = g e2 [ _施設介護収入,_通所介護訪問介護収入]
    f e2 (V事業所形態_医療福祉 E有料老人ホーム                    ) = g e2 [ _社会福祉事業収入]
    f e2 (V事業所形態_医療福祉 E更生保護事業                      ) = g e2 [ _社会福祉事業収入]
    f e2 (V事業所形態_医療福祉 Eその他の社会保険社会福祉介護事業  ) = g e2 [ _社会福祉事業収入]
    f e2 (V事業所形態_医療福祉 Eその他の障碍者福祉事業            ) = g e2 [ _社会福祉事業収入]
    f e2 Null                                                       = g e2 [ _保険診療収入
                                                                           , _保険外診療収入
                                                                           , _施設介護収入
                                                                           , _通所介護訪問介護収入
                                                                           , _社会保険事業収入
                                                                           , _保健衛生事業収入
                                                                           , _社会福祉事業収入]


-- *** サービス関連産業B
-----------------------------------------------------------
{- |
     サービス関連産業Bの主業及び従業の主生産物及び副生産物の把握は，事業所調査票，
     単独事業所調査票（サービス関連産業B）等における第２面調査項目「サービス関連産業Bの事業収入内訳」，
     「施設店舗等形態」，及び「物品賃貸業のレンタル年間売上高及びリース年間契約高」を主に用いて行われる。

     以下，本設に限り「サービス関連産業Bの事業収入内訳」を項目１，
     「施設店舗等形態」を項目２，「物品賃貸業のレンタル年間売上高及びリース年間契約高」を項目３と呼称する。

     項目１においては，「飲食業，宿泊サービス業，物品賃貸業，その他の生活関連サービス，スポーツ施設提供業」等の
     産業中分類程度の区分における事業別売上高と，
     それ以外のサービス業における産業細分類程度の区分における事業別売上高を調査している.
     なお,調査票においては,｢売上(収入金額) 又は割合｣と変換されているが,本稿に使用されているデータは
     金額のみである(割合のみの回答の結果が金額の値に補綴されているかは不明.)

     項目２では，産業細分類程度の区分主力事業の形態を調査している。物品賃貸業を除く，
     産業においては，項目1における区分が，「施設・店舗等形態」の区分範囲の場合
     (e.g 事業分類が宿泊事業, 店舗形態が旅館など,事業分類と店舗形態がマッチしている場合)
     は「施設・店舗等形態」の区分を(産業細分類に変換した上で)採用し，
     それ以外の場合は，事業分類を(産業細分類に変換した上で)主業の主生産物，副生産物として記録される。

     物品賃貸業においては，平成24，28年それぞれで処理が異なり，平成24年では，
     項目１の回答内容において産業区分が「産業機械，事務用機械，自動車，スポーツ・娯楽用品，
     その他（映画・演劇用品，音楽・映像記録物，貸衣しょう等）」の内３区分以上を含んでおり，
     且つ，当該部門の項目3における「レンタル年間売上高｣を「リース年間契約高」が上回った場合，
     物品賃貸業に該当する部門の売り上げを全て「総合リース業」の売上，
     下回った場合は「その他の各種物品賃貸業」の売上とする。同列あるいは,いずれもデータが存在しない場合はレンタルに割り振る.

     上記の条件を満たさない場合は，それぞれの項目を独立して物品賃貸業の生産物として記録する。
     項目１が未記入且つ，項目３が記載されている場合は，後者の割合から金額を算定し，同様の処理を行う。
     平成28年では，平成24年の条件に加えて，項目２の情報において
     「総合リース業，各種物品賃貸業，その他の物品賃貸業」の別を調査しており，
     その回答が「総合リース業，各種物品賃貸業」の場合は物品賃貸業に該当する項目１の売上高を，
     全額それらに分配し，「その他の物品賃貸業」の場合は，そのまま生産物として記録する。
     産業細分類は項目2における情報よりも荒いため,項目2を利用することで実際はより細かい情報が取れるがここではそれを行わない.

     主力事業が他の産業であり，項目２が物品賃貸業でない場合，24年と同等の条件で
     物品賃貸業に該当する項目１を処理し，副生産物として記録する。

    項目1及び,項目3それぞれにおける物品賃貸業の値に相違がある場合は,基本的には項目1を優先し,
    項目1,または項目3のいずれかが欠損している場合は他方を優先する.
    (同一の調査票内ですら重複情報を記入させるのはいかがなものか)
    (項目1あり/なし × 項目3あり/なし + 重複あり/なし で 6 パターンに分岐. 詳細は,コード参照)

    産業分類表に存在しない項目,
    784Z 恐らく公衆浴場格付け不能 及び 801Z 映画館格付け不能(?)の2項目に関しては追加し公衆浴場及び映画館として扱う.


-}

f産業格付_特殊な方法_サB :: Year -> IOCensusRow -> IO ()
f産業格付_特殊な方法_サB year icd = do
    -- 調査票の種類で，処理を行うか判定する
    kind <- readArray icd H調査票の種類
    case kind of
        V調査票の種類 x     | _対象産業 x == EサービスB         -> ifServiceB year icd
                            | otherwise                         -> return ()
        _                                                       -> return ()

    where
    -- サBだった場合の処理
    ifServiceB :: Year ->IOCensusRow -> IO ()
    ifServiceB year icr = do
        !man            <- readArray icd H管理補助的業務
        !comm           <- readArray icd H事業所別生産物別売上高
        !front          <- readArray icd H事業別売上高
        !shopType       <- readArray icd H店舗形態_サB
        !sal            <- readArray icd H事業収入_サB
        !rTotal         <- readArray icd Hレンタル総売上高
        !lTotal         <- readArray icd Hリース年間契約高
        !rSev           <- readArray icd H商品別レンタル売上高
        !lSev           <- readArray icd H商品別リース契約高

        !behind <- convNotSuiteVal <$> getValCarsFromVサB year man sal shopType rTotal lTotal rSev lSev
        mergeFrontAndBehind icr comm behind front ["T12", "T13", "T14", "T15", "T16", "T17", "T18", "T19", "T20"]


data RentalOrLease = Rental | Lease deriving (Eq, Show)

getValCarsFromVサB  :: Year
                    -> Val管理補助的業務
                    -> Val事業収入_サB
                    -> Val店舗形態_サB
                    -> Valレンタル総売上高
                    -> Valリース年間契約高
                    -> Val商品別レンタル売上高
                    -> Val商品別リース契約高
                    -> IO ValCars

getValCarsFromVサB year man sal shopType rTotal lTotal rSev lSev
    =  rateToManey rTotal rSev >>= \ rSevMoney
    -> rateToManey lTotal lSev >>= \ lSevMoney
    -> return $! VCars
              $! convMCinCars False man
              $! convertServiceB year sal shopType rTotal lTotal rSev lSev

    where
    -- 物品賃貸業のレンタル年間契約高及びリース年間契約高に基づいてCarsを作る
    -- あとで事業収入_サBのところとマージ(こっちに情報があれば,事業収入の物品賃貸業部分は破棄)

    -- | 割合の金額への変換
    rateToManey :: ValDouble    {- ^ Valレンタル総売上高 or Valリース年間契約高 -}
                -> ValCars      {- ^ 商品別レンタル売上高 or 商品別リース契約高 -}
                -> IO ValCars   {- ^ 商品別レンタル売上高 or 商品別リース契約高 -}
    rateToManey Null         _           = return Null
    rateToManey _            Null        = return Null
    rateToManey (VDouble dl) (VCars cs)  = VCars <$> V.mapM (\x -> let v = value x
                                                              in case (value x) <= 100.0 of
                                                                    True  -> return (x {value = 0.01 * dl * (value x)})
                                                                    False -> print ( "this value should be rate:" ++ ushow x) >> return x ) cs

    -- | 総合リース業(7011), その他の各種物品賃貸業(7019)への変換
    -- 三種以上含まれていれば,総合または各種
    convertToMulti :: Valレンタル総売上高
                   -> Valリース年間契約高
                   -> Val商品別レンタル売上高 {- ^ 金額に変換済み -}
                   -> Val商品別リース契約高   {- ^ 金額に変換済み -}
                   -> Cars事業所別生産物別売上高

    convertToMulti _            _             Null       Null         = V.empty
    convertToMulti _            _             Null       (VCars ls)
        = case isMaybeMulti ls of   Nothing     -> V.empty
                                    Just True   -> V.singleton $! Car (sumCars ls) (T.pack "7011")
                                    Just False  -> ls

    convertToMulti _            _             (VCars rs) Null
        = case isMaybeMulti rs of   Nothing     -> V.empty
                                    Just True   -> V.singleton $! Car (sumCars rs) (T.pack "7019")
                                    Just False  -> rs

    convertToMulti (VDouble rd) Null          (VCars rs) (VCars ls)
        = case isMaybeMulti rs of   Nothing     -> V.empty
                                    Just True   -> V.singleton $! Car (sumCars rs) (T.pack "7019")
                                    Just False  -> rs


    convertToMulti Null         (VDouble ld)  (VCars rs) (VCars ls)
        = case isMaybeMulti ls of   Nothing     -> V.empty
                                    Just True   -> V.singleton $! Car (sumCars ls) (T.pack "7011")
                                    Just False  -> ls


    convertToMulti Null         Null          (VCars rs) (VCars ls)
        = case (isMaybeMulti rs, isMaybeMulti ls) of
                (Nothing,       Nothing)        -> V.empty
                (Just False,    Nothing)        -> rs
                (Nothing,       Just False)     -> ls
                (Just True,     Nothing)        -> V.singleton (Car (sumCars rs) (T.pack "7019"))
                (Nothing,       Just True)      -> V.singleton (Car (sumCars ls) (T.pack "7011"))
                (Just False,    Just False)     -> rs V.++ ls
                (Just False,    Just True )     -> V.cons (Car (sumCars ls) (T.pack "7011"))  rs
                (Just True,     Just False)     -> V.cons (Car (sumCars rs) (T.pack "7019"))  ls
                (Just True,     Just True )     -> V.cons (Car (sumCars ls) (T.pack "7011"))  rs -- 決めうち


    convertToMulti (VDouble rd) (VDouble ld) (VCars rs) (VCars ls)
        = case (isMaybeMulti rs, isMaybeMulti ls) of
                (Nothing,       Nothing)        -> V.empty
                (Just False,    Nothing)        -> rs
                (Nothing,       Just False)     -> ls
                (Just True,     Nothing)        -> V.singleton (Car (sumCars rs) (T.pack "7019"))
                (Nothing,       Just True)      -> V.singleton (Car (sumCars ls) (T.pack "7011"))
                (Just False,    Just False)     -> rs V.++ ls
                (Just False,    Just True )     | rd <= ld  -> V.cons (Car (sumCars ls) (T.pack "7011"))  rs
                                                | otherwise -> rs V.++ ls
                (Just True,     Just False)     | rd >= ld  -> V.cons (Car (sumCars rs) (T.pack "7019"))  ls
                                                | otherwise -> rs V.++ ls
                (Just True,     Just True )     | rd >= ld  -> V.cons (Car (sumCars rs) (T.pack "7019"))  ls
                                                | otherwise -> V.cons (Car (sumCars ls) (T.pack "7011"))  rs


    -- | 三種以上入っているとTrue
    -- VIO の時点で,それぞれまとめられているので長さだけでいい.
    isMaybeMulti :: Cars -> Maybe Bool
    isMaybeMulti cs | V.null cs        = Nothing
                    | V.length cs >= 3 = Just True
                    | otherwise        = Just False

    -- | 総売上からレンタルかリースか判断(24年限定)
    -- 同列または,どちらもデータが存在しない場合はレンタル
    totalRorL :: Valレンタル総売上高 -> Valリース年間契約高 -> RentalOrLease
    totalRorL Null        Null                    = Rental
    totalRorL Null        (VDouble l)             = Lease
    totalRorL (VDouble r) Null                    = Rental
    totalRorL (VDouble r) (VDouble l) | r >= l    = Rental
                                      | otherwise = Lease


    -- | 物品賃貸業に関して,金額変換したものがNullなら,事業収入を用いる,この場合,総合リースや各種への対応は省略 (一般的な方法で自動でなるから)
    -- 上がNot Null なら,
    -- 上の値を用いる.
    -- 店舗形態範囲外ならそのまま変換, 範囲内なら形態番号を参照してマッチングすれば変換
    -- 店舗形態とマッチングしない,店舗形態がない場合は,範囲内格付け不明
    -- 28年の店舗形態による総合リース業及び,各種物品賃貸業への振替はここで行う

    convertServiceB :: Year
                    -> Val事業収入_サB
                    -> Val店舗形態_サB
                    -> Valレンタル総売上高
                    -> Valリース年間契約高
                    -> Val商品別レンタル売上高 {- ^ 金額に変換済み -}
                    -> Val商品別リース契約高   {- ^ 金額に変換済み -}
                    -> Cars事業所別生産物別売上高

    convertServiceB _  Null        _    r l vrs vls  = convertToMulti r l vrs vls

    convertServiceB 24 (VCars cb)  Null r l vrs vls
        =  let cbIs物品賃貸業 = V.filter ((VDC.is物品賃貸業  24) . name ) cb
        in case (isMaybeMulti cbIs物品賃貸業) of
            Nothing     -> (V.++) (convertToMulti r l vrs vls)
                        $! V.map (\x -> lookupShopType 24 x (T.pack "") gdサB事業収入_店舗形態24 gdサB事業収入_店舗形態不適合24) cb
            Just False  -> V.map (\x -> lookupShopType 24 x (T.pack "") gdサB事業収入_店舗形態24 gdサB事業収入_店舗形態不適合24) cb
            Just True   -> case (totalRorL r l) of
                                Lease  -> (V.cons) (Car (sumCars cbIs物品賃貸業) "7011")
                                       $! V.map  (\x -> lookupShopType 24 x (T.pack "") gdサB事業収入_店舗形態24 gdサB事業収入_店舗形態不適合24)
                                       $! V.filter (not . (VDC.is物品賃貸業 24) . name ) cb -- 二重計上しないためのfilter

                                Rental -> (V.cons) (Car (sumCars cbIs物品賃貸業) "7019")
                                       $! V.map  (\x -> lookupShopType 24 x (T.pack "") gdサB事業収入_店舗形態24 gdサB事業収入_店舗形態不適合24)
                                       $! V.filter (not . (VDC.is物品賃貸業 24) . name ) cb -- 二重計上しないためのfilter

    convertServiceB 24 (VCars cb) (VText tx) r l vrs vls
        =  let cbIs物品賃貸業 = V.filter ((VDC.is物品賃貸業  24) . name ) cb
        in case (isMaybeMulti cbIs物品賃貸業) of
            Nothing     -> (V.++) (convertToMulti r l vrs vls)
                        $! V.map (\x -> lookupShopType 24 x tx gdサB事業収入_店舗形態24 gdサB事業収入_店舗形態不適合24) cb
            Just False  -> V.map (\x -> lookupShopType 24 x tx gdサB事業収入_店舗形態24 gdサB事業収入_店舗形態不適合24) cb
            Just True   -> case (totalRorL r l) of
                                Lease  -> (V.cons) (Car (sumCars cbIs物品賃貸業) "7011")
                                       $! V.map (\x -> lookupShopType 24 x tx gdサB事業収入_店舗形態24 gdサB事業収入_店舗形態不適合24)
                                       $! V.filter (not . (VDC.is物品賃貸業 24) . name ) cb

                                Rental -> (V.cons) (Car (sumCars cbIs物品賃貸業) "7019")
                                       $! V.map (\x -> lookupShopType 24 x tx gdサB事業収入_店舗形態24 gdサB事業収入_店舗形態不適合24)
                                       $! V.filter (not . (VDC.is物品賃貸業 24) . name ) cb

    convertServiceB 28   (VCars cb) Null r l vrs vls
         =  let cbIs物品賃貸業 = V.filter ((VDC.is物品賃貸業  28) . name ) cb
        in case (isMaybeMulti cbIs物品賃貸業) of
                    Nothing     -> (V.++) (convertToMulti r l vrs vls)
                                $! V.map (\x -> lookupShopType 28 x (T.pack "") gdサB事業収入_店舗形態28 gdサB事業収入_店舗形態不適合28) cb
                    Just False  -> V.map (\x -> lookupShopType 28 x (T.pack "") gdサB事業収入_店舗形態28 gdサB事業収入_店舗形態不適合28) cb
                    Just True   -> case (totalRorL r l) of
                                        Lease  -> (V.cons) (Car (sumCars cbIs物品賃貸業) "7011")
                                               $! V.map (\x -> lookupShopType 28 x (T.pack "") gdサB事業収入_店舗形態28 gdサB事業収入_店舗形態不適合28)
                                               $! V.filter (not . (VDC.is物品賃貸業 28) . name ) cb

                                        Rental -> (V.cons) (Car (sumCars cbIs物品賃貸業) "7019")
                                               $! V.map (\x -> lookupShopType 28 x (T.pack "") gdサB事業収入_店舗形態28 gdサB事業収入_店舗形態不適合28)
                                               $! V.filter (not . (VDC.is物品賃貸業 28) . name ) cb

    convertServiceB 28   (VCars cb) (VText tx)  r l vrs vls
        =  let cbIs物品賃貸業 = V.filter ((VDC.is物品賃貸業  28) . name ) cb
        in case (isMaybeMulti cbIs物品賃貸業) of
                    Nothing     -> (V.++) (convertToMulti r l vrs vls)
                                $! V.map (\x -> lookupShopType 28 x tx gdサB事業収入_店舗形態28 gdサB事業収入_店舗形態不適合28) cb
                    Just False  -> V.map (\x -> lookupShopType 28 x tx gdサB事業収入_店舗形態28 gdサB事業収入_店舗形態不適合28) cb
                    Just True   -> V.map (\x -> lookupShopType 28 x tx gdサB事業収入_店舗形態28 gdサB事業収入_店舗形態不適合28) cb -- 店舗形態番号を利用して自動で総合リース/各種物品賃貸業を分類


    --  | 事業収入番号と店舗形態番号がマッチしているかに応じて,産業細分類に変換する
    lookupShopType :: Year -> Car -> Text店舗形態番号 -> M店舗形態適合マップ -> M店舗形態不適合マップ -> Car
    lookupShopType year ca txShopNum mp1 mp2
            | VDC.is店舗範囲 year txShopNum     =  case Map.lookup ((name ca),txShopNum) mp1 of
                                                    Just newName -> Car (value ca) newName
                                                    Nothing      -> case Map.lookup (name ca) mp2 of
                                                                        Just newName2 -> Car (value ca) newName2
                                                                        Nothing       -> Car (value ca) (T.pack "R2ZZ")
            | otherwise                         =  case Map.lookup (name ca) mp2 of
                                                    Just newName -> Car (value ca) newName
                                                    Nothing      -> Car (value ca) (T.pack "R2ZZ")


type Text店舗形態番号 = Text
type Text事業収入番号 = Text

-- | 事業収入番号と店舗形態がマッチ(e.g 宿泊業, 旅館ホテル)しているかを判定
type M店舗形態適合マップ     = Map (Text事業収入番号,Text店舗形態番号) IndustryDetail

-- | 店舗形態と事業収入のペアがM店舗形態適合マップの中にない場合に,事業収入を産業分類細分類に振り返るマップ
type M店舗形態不適合マップ   = Map Text事業収入番号 IndustryDetail


-- *** 協同組合
-----------------------------------------------------------
{- |
     協同組合は，平成24，28年共に，単独事業所調査票及び，事業所調査票（協同組合）において調査されており，
     単独事業所調査票では，調査項目「協同組合の種類」において
     「農業協同組合，行業協同組合，水産加工業協同組合，森林組合，事業協同組合，その他の事業協同組合（1~5の協同組合以外）」
     のうち一つを回答する形式の調査を行っている．

     また，事業所調査票においてはそれに追加して，「信用事業又は共済事業の実施の有無」を調査している．

     産業連関表では，協同組合の収益の配分先は，
     「農林水産金融業，卸売，小売，倉庫，対企業民間非営利団体」の５産業であり，
     協同組合それ自体の産業区分は存在しない．
     それに準じて，組替集計においては，協同組合の収益をこれらの産業に区分して記録する．

     「調査票の記入の仕方」に従えば，事業別売上高において，協同組合の賦課金は，「政治・経済・文化団体の活動収入」に含まれるため，
     分類された協同組合の種類に「政治・経済・文化団体の活動収入」の収入金額を全額計上する．

     事業所調査票では，「協同組合の種類」において「農業協同組合，漁業協同組合，水産加工業協同組合，森林組合」の何れかが選択され，

     また，「信用事業又は共済事業の実施の有無」において「行っている」が選択されている場合に，
     「事業別売上（収入）金額」における「金融，保険事業の収入」を全額「農林水産金融業」に記録する．

    「行っていない」が選択されている場合は，「金融業，保険業内格付け不可」に記録する．

     また，「卸売の商品販売額（代理・仲立手数料を含む）」を全て卸売業，「小売りの商品販売額」を全て小売業に記録し，
     「運輸・郵便事業の収入」を全て「倉庫業」に記録する．

     「協同組合の種類」において，「その他の事業協同組合」が選択された場合は，
     「事業所の売上（収入）金額」又は，「事業別売上（収入）金額」の合計額を「事業協同組合（他に分類されないもの）」に記録する．

     単独事業所調査票では，「協同組合の種類」の回答が等しい事業所調査票の「協同組合の種類」が等しい事業所の案分比率を用いて，
     「事業別売上（収入）金額」における「金融，保険事業の収入」の値を按分する．

     双方において「協同組合の種類」の回答がない場合は，
     「協同組合（他に分類されないもの） 内格付不能」に全額を記録し，他の事業所の主業副業副産物主生産物の比率を用いて，売上高を按分する．

-}


f産業格付_特殊な方法_協同組合 :: IOCensusRow -> IO ()
f産業格付_特殊な方法_協同組合 icd = do
    -- 調査票の種類で，処理を行うか判定する
    kind <- readArray icd H調査票の種類
    case kind of
        V調査票の種類 x     | _対象産業 x == E協同組合  -> ifSuite icd
                            | otherwise                 -> return ()
        _                                               -> return ()

    where
    -- | 医療福祉だった場合の処理
    ifSuite :: IOCensusRow -> IO ()
    ifSuite icr = do
        !man   <- readArray icd H管理補助的業務
        !comm  <- readArray icd H事業所別生産物別売上高
        !front <- readArray icd H事業別売上高
        !kind  <- readArray icd H協同組合の種類
        !bl    <- readArray icd H信用共済事業の有無
        !sales <- readArray icd H事業別売上高
        -- 軽くするため，使用しない項目に関してはNullにしてもいいかもしれない（要件等）

        let behind = convNotSuiteVal (getValCarsFromV協同組合 man kind bl sales)
        mergeFrontAndBehind icr comm behind front ["T20"]


{- | E事業所形態_医療福祉 に対応する E事業収入_医療福祉 のフィールド名（関数）を返す

    事業別売上高の

    運輸業 -> 倉庫

    金融業 -> 農林水産金融業

    政治・経済・文化団体 -> 協同組合

    にそれぞれ配分(卸売り小売りは，一般的な方法で分解されるので何もしない)

 -}

getValCarsFromV協同組合 ::Val管理補助的業務 ->  Val協同組合の種類 ->  Val信用共済事業の有無 -> Val事業別売上高 -> ValCars
getValCarsFromV協同組合 man kind bl sales = f kind bl sales
    where
    -- | 事業別売上高から値を抽出
    projSales :: String -> Cars -> Double
    projSales str cs = V.sum $! V.map value $! V.filter (\x -> name x == T.pack str)  cs
    -- | 運輸
    ~trans  = projSales "T9"
    -- | 金融業
    ~fns    = projSales "T10"
    -- | 協同組合
    ~coop   = projSales "T11"

    -- | 管理補助的業務の対応
    g = (convMCinCars False man) . V.fromList

    f ::  Val協同組合の種類 ->  Val信用共済事業の有無 -> Val事業別売上高 -> ValCars
    f Null  Null            Null              = Null
    f Null  Null            (VCars cs)        = VCars $! g [Car (coop cs)  (T.pack "87ZZ")]
    f Null  (VBool True )   Null              = VCars $! g [Car 0 (T.pack "6320")]
    f Null  (VBool False)   Null              = VCars $! g [Car 0 (T.pack "87ZZ")]
    f Null  (VBool True )   (VCars cs)        = VCars $! g [ Car (trans cs) (T.pack "4710"), Car (coop  cs) (T.pack "87ZZ"), Car (fns cs) (T.pack "6320")]
    f Null  (VBool False)   (VCars cs)        = VCars $! g [ Car (trans cs) (T.pack "4710"), Car (coop  cs) (T.pack "87ZZ")]
    f k     Null            Null              = VCars $! g [ Car 0 (getName k)]
    f k     Null            (VCars cs)        = VCars $! g [ Car (trans cs) (T.pack "4710"), Car (coop  cs) (getName k)]
    f k     (VBool True )   Null              = VCars $! g [ Car 0 (T.pack "4710") , Car 0 (getName k) , Car 0 (T.pack "6320")]
    f k     (VBool False)   Null              = VCars $! g [ Car 0 (T.pack "4710") , Car 0 (getName k)]
    f k     (VBool True )   (VCars cs)        = VCars $! g [ Car (trans cs) (T.pack "4710"), Car (coop  cs) (getName k), Car (fns cs) (T.pack "6320")]
    f k     (VBool False)   (VCars cs)        = VCars $! g [ Car (trans cs) (T.pack "4710"), Car (coop  cs) (getName k)]
    f _     _               _                 = Null

    getName :: Val協同組合の種類 -> Text
    getName Null                 = T.pack "87ZZ"
    getName (V協同組合の種類 x)  = case Map.lookup x edE協同組合の種類 of
                                        Just n  -> n
                                        Nothing -> error "can Not find in edE協同組合の種類"


-- *** サービス関連産業A：金融業，保険業，郵便局受託行，政治・経済・文化団体
-----------------------------------------------------------
{- | サービスAと建設は同一の調査項目に関わるので同時に処理する.

    * サービスA
     電気，ガス，熱供給，水道業，運輸業，郵便業，通信，放送，映像・音声・文字情報制作業は，
    平成24年単独事業所調査票，企業調査票，事業所調査票（建設業，サービス関連産業A），
    平成28年単独事業所調査票，企業調査票，事業所調査票（建設業，サービス関連産業A，学校教育）において調査されており，

    事業所調査票では「事業の種類」を選択し，単独事業所調査票及び企業調査票においては，調査項目「主な事業収入の内訳」にて，
    第10位までの細分類相当の「事業内容及び売上（収入）金額又は割合」を把握している．

    サービス関連産業Aはネットワーク産業であり，事業所調査票は集計対象とならないため，「主な事業収入の内訳」の値を直接企業別生産物別売上高として利用する．


    * 建設
    平成24，28年経済センサス企業調査票（建設業，サービス関連産業A）における建設業においては，
    調査票裏面「15 主な事業収入の内訳」で
    「土木工事，住宅建築工事・同設備工事，非住宅建築工事・同設備工事，機械設備工事」のそれぞれ
    「元請，下請け」別（以下，建築8区分と呼称）に該当する売上収入金額または割合を記入する．

    また，「16 業態別工事種類」において，
    建築業法の工種区分を一部細分化した33種類の業態の内年間における完成工事高上位２種を選択する形式となっている．
    一方，事業所調査票（建設業，サービス関連産業A）においては，
    調査項目「事業の種類」においては，前述の33区分工種に，「一般土木建築工事」を加えた34区分からの選択式になっている．

     組替集計のために必要となる作業は企業調査票における調査項目２つから，
     建設業における主業の主生産物及び副生産物を明らかにし，その比率を単独事業所調査票（建設，サービス業A）及び，
     「事業別売上（収入）金額」において，
     「建設事業の収入」に記載のあった事業所の副業の主生産物及び副生産物比率を把握することである．
     ここでは，経済センサス集計における産業格付けの「特殊な方法」に則りながら，主業の主生産物及び副生産物の売上高を把握する．

     対処方針として，建築8区分の売上額を工種区分で記載されている職種に配分し，
     その後，工種区分とセンサス細分類の対応表を利用してセンサス小分類に配分する．
     なお，センサス細分類における「一般土木建築工事業」には，建築8区分における「土木工事」，
     「住宅建築工事・同設備工事又は非住宅建築工事・同設備工事」が共に記載されている事業所，あるいは，工種区分において，
     「土木一式工事」及び「建築一式工事，又は木造建築一式工事」の双方が選択されている事業所から，
     事業所調査票における記載「一般土木建築工事（完成工事高において建築工事の占める割合が２割以上，8割未満）」，
     「土木一式工事（完成工事高において建築工事の占める割合が２割未満）」，
     「建築一式工事（完成工事高において建築工事の占める割合が8割以上）」に従って，分類する．

    なお,事業別売上(収入)金額の内訳における,下請け工事部分は,二重計上を避けるため,後に削除するが,各事業所単位では削除しない.


    * 金融業,保険業
    金融業，保険業は，平成24年では単独事業書調査票，企業調査票，事業所調査票（建設業，サービス関連産業A），
    平成28年では，単独事業書調査票，企業調査票，事業所調査票（建設業，サービス関連産業A，学校教育）において調査されており，
    いずれの場合でも，調査項目「金融業，保険業の事業種類」において，該当する事業種類を調査している．

    金融業，保険業はネットワーク産業であるため，企業及び単独事業所を集計対象とし，
    複数事業所からなる企業における事業所単位での集計は行わない．
     企業別生産物別売上高の把握に当たっては企業調査票，
     団体調査票において選択された種類に調査項目「事業別売上（収入）金額」における「金融，保険業の収入」の回答金額を全額載せる．
     企業調査票における解答欄において複数の回答があった場合，
     傘下事業所における事業所調査票の調査項目「事業の種類」別に事業所別従業員数の比率を掛けて企業別業種別売上高を出す．
     案分後も差が出ない場合は，業種内格付け不可とする． 単独事業所調査票において回答が複数となった場合には，業種内格付け不可とする．


    *学校教育
    学校教育は，平成24年経済センサスでは，学校教育は，単独事業所調査票（学校教育），
    企業調査票（学校教育），事業所調査票（学校教育）の三つの調査票によって調査されている．
    このうち，企業調査票においては，調査項目「学校等種類別収入内訳」において学校等種類別の売上（収入）金額，
    または割合を調査し，企業調査票以外では，
    調査項目「学校等の種類」において事業所の主な事業として該当する学校等の種類のみを把握している．

     平成28年経済センサスでは，学校教育は，単独事業著調査票，企業調査票，
     事業所調査票（建設，サービス関連産業A，学校教育）において調査されており，
     そのうち企業調査票においては調査項目「学校等種類別収入内訳」において学校等種類別の，
     売上（収入）金額又は割合を調査しており，その他の調査票では学校等の種類のみを調査している．

     いずれの年度においても，学校教育はネットワーク型産業であるため，以降，事業所調査票の値を用いない．
     企業調査票の値は，そのまま事業所別生産物別売上高として用いて，単独事業書調査票は，
     選択されている学校の種類に，22区分の事業別売上（収入）金額における，「学校教育」の額を全額載せて，
     事業所別生産物別売上高として用いる．


    * 団体
    政治・経済・文化団体，宗教は，平成24年単独事業書調査票，
    企業調査票，事業所調査票（建設業，サービス関連産業A），
    平成28年単独事業所調査票，団体調査票，
    事業所調査票（政治・経済・文化団体，宗教）における調査項目「政治・経済・文化団体，宗教の種類」において，
    9つの形態から一つを選択する形式で調査を行っている．
    「政治・経済・文化団体，宗教」はネットワーク産業であるため，
    企業及び団体，単独事業所を集計対象とし，複数事業所からなる企業，
    団体における事業所単位での集計は行わない．
     企業別生産物別売上高の把握に当たっては企業調査票，
     団体調査票において選択された種類に調査項目「事業別売上（収入）金額」における
     「政治・経済・文化団体，宗教（団体）」の回答金額を全額載せる．
     企業調査票，団体調査票における解答欄において複数の回答があった場合，
     傘下事業所における事業所調査票の調査項目「事業の種類」別に事業所別従業員数の比率を掛けて企業別業種別売上高を出す．
     案分後も差が出ない場合は，業種内格付け不可とする． 単独事業所調査票において回答が複数となった場合には，
     業種内格付け不可とする．
-}

f産業格付_特殊な方法_建サA :: Year  -> IOCensusRow -> IO ()
f産業格付_特殊な方法_建サA year icd =  do
    -- 調査票の種類で，処理を行うか判定する
    kind <- readArray icd H調査票の種類
    case kind of
        V調査票の種類 x     | _対象産業 x == E建設サービスA     -> ifSuite year icd
                            | _対象産業 x == E建設サービスA学校 -> ifSuite year icd
                            | _対象産業 x == E団体              -> ifSuite year icd
                            | _対象産業 x == E学校教育          -> ifSuite year icd
                            | otherwise                         -> return ()
        _                                                       -> return ()

    where
    -- | 建設サービスAだった場合の処理
    ifSuite :: Year -> IOCensusRow -> IO ()
    ifSuite year icr = do
        !man            <- readArray icd H管理補助的業務
        !comm           <- readArray icd H事業所別生産物別売上高
        !consKind       <- readArray icd H工事種類
        !sal            <- readArray icd H事業収入_建サA
        !front          <- readArray icd H事業別売上高
        !orgKind        <- readArray icd H団体の種類
        !finKind        <- readArray icd H金融業保険業の事業種類
        !schKind        <- readArray icd H学校等の種類
        !schIncome      <- readArray icd H収入内訳_学校
        !mainKind       <- readArray icd H主な事業の種類

        let behind = convNotSuiteVal (getValCarsFromV建サA year man consKind sal front orgKind finKind schKind schIncome mainKind)
        mergeFrontAndBehind icr comm behind front ["T6", "T7", "T8", "T9", "T11"]

-- | f産業格付_特殊な方法_建サA の内部関数
--
-- H事業収入_建サA  は建設とサAを処理,それ以外の項目は独自に処理して最後に結合
--
-- 関数ごとに分割するべき（課題）


getValCarsFromV建サA :: Year
                     -> Val管理補助的業務
                     -> Val工事種類
                     -> Val事業収入_建サA
                     -> Val事業別売上高
                     -> Val団体の種類
                     -> Val金融業保険業の事業種類
                     -> Val学校等の種類
                     -> Val収入内訳_学校
                     -> Val主な事業の種類
                     -> ValCars

getValCarsFromV建サA year man consKind sal sev orgKind finKind schKind schIncome mainKind
    = VCars $! seARes V.++ cnsRes V.++ orgRes V.++ finRes V.++ schRes V.++ sinRes
    where
    -- | 建設分だけを抜き出す
    (~cns, ~seA)   = partCns year sal
    -- | サA部分
    ~seARes = convOther year seA
    -- | 建設部分
    ~cnsRes = convCns year consKind (VCars cns) sev
    -- | 団体の種類部分
    ~orgRes = convOrg orgKind sev
    -- | 金融保険業部分
    ~finRes = convFin finKind sev
    -- | 学校教育の部分
    ~schRes = convSch schIncome sev
    -- | その他
    ~sinRes = convForSingles year schKind mainKind

    -- 以下, 関数 -----------------------------------------------------
    -- | 管理補助的業務の対応
    forMC = convMCinCars False man

    -- | 建設業とそれ以外で分離する
    partCns :: Year -> Val事業収入_建サA -> (Cars, Cars)
    partCns year Null                   = (V.empty, V.empty)
    partCns year (VCars cs)             = let f x = is建設 year (name x) in   (V.filter f cs, V.filter (not . f) cs)
    partCns year _                      = (V.empty, V.empty)


    -- | 建設以外の部分の変換 (seAに適用する)
    convOther :: Year -> Cars -> Cars
    convOther 24 cs = lookupCarsNameErr cs gdサービスA24
    convOther 28 cs = lookupCarsNameErr cs gdサービスA28



    -- | 建設だけのCarsを作る >> サAだけのCarsと結合した上で,convMCinCarsを適用して結果にする.
    -- 33区分に8区分を配分する.
    -- 8区分ごとに,1番目と2番目になれるかを判定
    -- 片方にのみなれる場合は全額そちらに配分
    -- 両方になれる場合は1番めに60%,二番目に40%を配分する
    -- いずれにもなれない場合は,格付け不能に配分
    ~cnsCNC = Car 0 (T.pack "DZZ0")

    convCns :: Year -> Val工事種類 -> Val事業収入_建サA -> Val事業別売上高 ->  Cars
    convCns year Null  Null       Null          = forMC $! V.empty
    convCns year Null  (VCars cs) _             = forMC $! V.singleton $! Car (VDS.sumCars cs) (T.pack "DZZ0")
    convCns year Null  Null       (VCars cs)    =  let v = VDS.getValofCars (T.pack "T6") (VCars cs)
                                                in forMC $! V.singleton $! Car v (T.pack "DZZ0")


    convCns year (V工事種類  (E工事種類 c1 c2))  Null Null
        = case (Map.lookup c1 gd建設, Map.lookup c2 gd建設) of
            (Just x,  Just y ) -> forMC $! V.singleton $! Car 0 x
            (Just x,  Nothing) -> forMC $! V.singleton $! Car 0 x
            (Nothing, Just y ) -> forMC $! V.singleton $! Car 0 y
            (Nothing, Nothing) -> forMC $! V.singleton cnsCNC

    convCns year (V工事種類  (E工事種類 c1 c2))  Null  (VCars cs)
        = let v = VDS.getValofCars (T.pack "T6") (VCars cs)
        in case (Map.lookup c1 gd建設, Map.lookup c2 gd建設) of
            (Just x,  Just y ) -> forMC $! V.fromList [Car (0.6 * v) x, Car (0.4 * v) y]
            (Just x,  Nothing) -> forMC $! V.singleton $! Car v x
            (Nothing, Just y ) -> forMC $! V.singleton $! Car v y
            (Nothing, Nothing) -> forMC $! V.singleton cnsCNC

    convCns year (V工事種類  (E工事種類 c1 c2))  (VCars cs)  _
        = forMC $! runST $ do
            case (Map.lookup c1 gd建設, Map.lookup c2 gd建設) of
                (Just x,  Just y ) -> do
                    car1 <- newSTRef (Car 0 x)  :: ST s0 (STRef s0 Car)
                    car2 <- newSTRef (Car 0 y)  :: ST s0 (STRef s0 Car)
                    cnc  <- newSTRef cnsCNC     :: ST s0 (STRef s0 Car)
                    forM (V.toList cs) $ \c -> do
                        let v = value c
                        let n = name  c
                        case (canBe33 year n c1, canBe33 year n c2) of
                            (False, False) -> modifySTRef cnc  (addValueCar v)
                            (True,  False) -> modifySTRef car1 (addValueCar v)
                            (False, True ) -> modifySTRef car2 (addValueCar v)
                            (True,  True ) -> modifySTRef car1 (addValueCar (0.6 * v))
                                           >> modifySTRef car2 (addValueCar (0.4 * v))
                    res1 <- readSTRef car1
                    res2 <- readSTRef car2
                    res3 <- readSTRef cnc
                    return $! forMC $ V.fromList [res1,res2,res3]

                (Just x,  Nothing) -> do
                        car1 <- newSTRef (Car 0 x)  :: ST s0 (STRef s0 Car)
                        cnc  <- newSTRef cnsCNC     :: ST s0 (STRef s0 Car)
                        forM (V.toList cs) $ \c -> do
                            let v = value c
                            let n = name  c
                            case (canBe33 year n c1) of
                                False -> modifySTRef cnc (addValueCar v)
                                True  -> modifySTRef car1 (addValueCar v)

                        res1 <- readSTRef car1
                        res3 <- readSTRef cnc
                        return $! forMC $ V.fromList [res1,res3]

                (Nothing, Just y ) -> do
                        car2 <- newSTRef (Car 0 y)  :: ST s0 (STRef s0 Car)
                        cnc  <- newSTRef cnsCNC     :: ST s0 (STRef s0 Car)
                        forM (V.toList cs) $ \c -> do
                            let v = value c
                            let n = name  c
                            case (canBe33 year n c1) of
                                False -> modifySTRef cnc (addValueCar v)
                                True  -> modifySTRef car2 (addValueCar v)

                        res2 <- readSTRef car2
                        res3 <- readSTRef cnc
                        return $! forMC $ V.fromList [res2,res3]

                (Nothing, Nothing) -> do
                        cnc  <- newSTRef cnsCNC     :: ST s0 (STRef s0 Car)
                        forM (V.toList cs) $ \c -> do
                            let v = value c
                            let n = name  c
                            modifySTRef cnc (addValueCar v)

                        res3 <- readSTRef cnc
                        return $! forMC $ V.singleton res3

    -- |                 8区分      33区分
    canBe33 :: Year -> Text -> Text -> Bool
    canBe33 24 c8 c33   =  let  looked  = Map.lookup c8 ss建設分配24
                        in case looked of
                         Just x    -> L.elem c33 x
                         Nothing   -> error $! "error :" ++ (ushow c8) ++ "is not a correct value"
    canBe33 28 c8 c33   =  let  looked  = Map.lookup c8 ss建設分配28
                        in case looked of
                         Just x    -> L.elem c33 x
                         Nothing   -> error $! "error :" ++ (ushow c8) ++ "is not a correct value"



    -- | 団体の種類の対応
    -- 事業別売上高を入れるだけ
    ~orgCNC = Car 0 (T.pack "9390")  -- 他に分類されない非営利的団体
    convOrg :: Val団体の種類 -> Val事業別売上高 -> Cars
    convOrg Null            Null          = V.empty
    convOrg Null            (VCars cs)    = forMC $! V.singleton $! addValueCar (VDS.getValofCars (T.pack "T11") (VCars cs) ) orgCNC
    convOrg (V団体の種類 x) Null          = case Map.lookup x edE団体の種類 of
                                             Just n  -> forMC $! V.singleton $! Car 0 n
                                             Nothing -> forMC $! V.singleton $! orgCNC

    convOrg (V団体の種類 x) (VCars cs)    = case Map.lookup x edE団体の種類 of
                                             Just n  -> forMC $! V.singleton $! Car (VDS.getValofCars (T.pack "T11") (VCars cs) ) n
                                             Nothing -> forMC $! V.singleton $! addValueCar (VDS.getValofCars (T.pack "T11") (VCars cs) ) orgCNC

    -- | 金融保険業の対応
    ~finCNC = Car 0 (T.pack "JZZ0") --  金融業，保険業 内格付不能
    convFin :: Val金融業保険業の事業種類 -> Val事業別売上高 -> Cars
    convFin Null        Null        = V.empty
    convFin Null        (VCars cs)  = forMC $! V.singleton $! addValueCar (VDS.getValofCars (T.pack "T10") (VCars cs) ) finCNC

    convFin (VText x)   Null        = case Map.lookup x gd金融保険 of
                                             Just n  -> forMC $! V.singleton $! Car 0 n
                                             Nothing -> forMC $! V.singleton $! finCNC

    convFin (VText x)   (VCars cs)  = case Map.lookup x gd金融保険 of
                                             Just n  -> forMC $! V.singleton $! Car (VDS.getValofCars (T.pack "T10") (VCars cs) ) n
                                             Nothing -> forMC $! V.singleton $! addValueCar (VDS.getValofCars (T.pack "T10") (VCars cs) ) finCNC

    -- | 学校教育の対応
    ~schCNC = Car 0 (T.pack "81ZZ") -- 学校教育 内格付不能
    -- | 事業別収入_学校教育はそのまま使える. 事業分類小分類に変換済み
    convSch :: Val収入内訳_学校 -> Val事業別売上高 -> Cars
    convSch Null        Null        = forMC $! V.singleton $! schCNC
    convSch Null        (VCars cs)  = forMC $! V.singleton $! addValueCar (VDS.getValofCars (T.pack "T21") (VCars cs) ) schCNC
    convSch (VCars cs)   _          = forMC $! cs


    -- | 主な事業の種類対応, 学校等の種類
    --  (これがNullでない = 事業所調査票 値が手に入らないのでそのまま,値ゼロのものを作る
    convForSingles :: Year -> Val学校等の種類   -> Val主な事業の種類 -> Cars
    convForSingles 24 Null      (VText y) = case Map.lookup y gd主な事業の種類24 of
                                            Just n  -> forMC $! V.singleton $! Car 0 n
                                            Nothing -> V.empty

    convForSingles 28 Null      (VText y) = case Map.lookup y gd主な事業の種類24 of
                                            Just n  -> forMC $! V.singleton $! Car 0 n
                                            Nothing -> V.empty

    convForSingles 24 (VText x) (VText y) = case (Map.lookup x gd学校教育24, Map.lookup y gd主な事業の種類24) of
                                            (Just xn, Just yn)  -> forMC $! V.fromList $! [Car 0 xn, Car 0 yn]
                                            (Just xn, Nothing)  -> forMC $! V.singleton $! Car 0 xn
                                            (Nothing, Just yn)  -> forMC $! V.singleton $! Car 0 yn
                                            (Nothing, Nothing)  -> V.empty

    convForSingles 28 (VText x) (VText y) = case Map.lookup y gd主な事業の種類24 of
                                            Just n  -> forMC $! V.singleton $! Car 0 n
                                            Nothing -> V.empty

    convForSingles _ (VText x)  Null      = case Map.lookup x gd学校教育24 of
                                            Just n  -> forMC $! V.singleton $! Car 0 n
                                            Nothing -> V.empty

    convForSingles _ Null       Null      = V.empty


-- *** その他全て
------------------------------------------------------------------
-- | 事業別売上高を事業所別生産物別売上高に振り替える

f産業格付_特殊な方法_その他 :: Year -> IOCensusRow -> IO ()
f産業格付_特殊な方法_その他 year icd = do
        !kind           <- readArray icd H調査票の種類
        case kind of
            Null                                                            -> forOther year icd
            V調査票の種類 x             | _調査票 x   == E産業共通調査票    -> forOther year icd
                                        | _対象産業 x == E全産業            -> forOther year icd
                                        | _対象産業 x == E産業なし          -> forOther year icd
                                        | _対象産業 x == E共通              -> forOther year icd
                                        | otherwise                         -> return ()
            _                                                               -> return ()


        where
        forOther :: Year -> IOCensusRow -> IO ()
        forOther year icr = do
            !comm           <- readArray icd H事業所別生産物別売上高
            !front          <- readArray icd H事業別売上高
            let behind = convertB2D front
            mergeFrontAndBehind icr comm behind front []

-- | 表面情報を裏面情報に変換する
{-# INLINE convertB2D #-}
convertB2D :: Val事業別売上高 -> Val事業所別生産物別売上高
convertB2D Null       = Null
convertB2D (VCars cs) = VCars
                      $ (flip V.map) cs
                      $ \(Car v n) ->  case (Map.lookup n VDC.bd格付け不能) of
                                        Nothing   -> Car 0 (T.pack "△△△△")
                                        Just newN -> Car v newN

-- | 副業の分解との重複を避けるために裏面の内容に関連するもののみを変換したものを返す
{-# INLINE convertB2DExclude #-}
convertB2DExclude :: Val事業別売上高 -> [IndustryBusiness] -> Val事業所別生産物別売上高
convertB2DExclude Null       _  = Null
convertB2DExclude x          [] = Null
convertB2DExclude (VCars cs) xs = convertB2D
                                $ VCars
                                $ (flip V.filter) cs
                                $ \(Car v n) -> (L.elem n xs)




-- | 裏面の取得情報と表面の事業別売上高を結合させる
{-# INLINE mergeFrontAndBehind #-}
mergeFrontAndBehind :: IOCensusRow
                    -> Val事業所別生産物別売上高    -- ^ もともとのもの
                    -> Val事業所別生産物別売上高    -- ^ 裏面から取得されたもの
                    -> Val事業別売上高
                    -> [IndustryBusiness]           -- ^ 裏面で扱っている表面の分類
                    -> IO ()

mergeFrontAndBehind icr _           Null        Null          _
    = return ()

mergeFrontAndBehind icr Null        (VCars new) front         xs
    = case V.null new of
        False -> writeArray icr H事業所別生産物別売上高 (VCars new)
        True  -> case (convertB2DExclude front xs) of
                    Null                -> writeArray icr H事業所別生産物別売上高 Null
                    (VCars fromSev)     -> writeArray icr H事業所別生産物別売上高 (VCars fromSev)

mergeFrontAndBehind icr Null        Null        front         xs
    = writeArray icr H事業所別生産物別売上高 (convertB2DExclude front xs)

mergeFrontAndBehind icr (VCars old) (VCars new) Null          _
    = writeArray icr H事業所別生産物別売上高 (VCars ((V.++) old new))

mergeFrontAndBehind icr (VCars old) (VCars new) (VCars seb)   xs
    = case V.null new of
        False -> writeArray icr H事業所別生産物別売上高  $VCars $ (V.++) old new
        True  -> case (convertB2DExclude (VCars seb) xs) of
                    Null                -> return ()
                    (VCars fromSev)     -> writeArray icr H事業所別生産物別売上高 $ VCars $ (V.++) old fromSev



-----------------------------------------------------------
-- *  価格変換
-----------------------------------------------------------
-- | 平成24年消費税率
ctr24 = 1.05


-- | ファイルを受け取って価格変換を行ったあと出力
full価格変換 :: InputFile -> Double -> Year -> IO ()
full価格変換 inputFile maxRowNum year   = runConduitRes
                                        $ sourceCensus inputFile
                                        .| f価格変換 year .| sinkCensus maxRowNum outputFile
                                where
                                outputFile = (((init. init . init . init) inputFile) ++ "ConvertPrice.csv")

{-| *「統計調査における売上高等の集計に係る消費税の取り扱いに関するガイドライン（
    平成27年５月19日 各府省統計主管課長等会議申し合せ）」に基づき処理を行う
    -}

f価格変換 :: (MonadIO m) =>  Year -> ConduitT IOCensusRow IOCensusRow m ()
f価格変換 28    =  await >>= \ maybeIcd
                -> case maybeIcd of
                    Nothing  -> return ()
                    Just icd -> yield icd >> f価格変換 28
f価格変換 24    =  await >>= \ maybeIcd
                -> case maybeIcd of
                    Nothing   -> return ()
                    Just icr  -> liftIO (f価格変換_事業別売上高              ctr24 icr)
                              >> liftIO (f価格変換_総売上                    ctr24 icr)
                              >> liftIO (f価格変換_費用等の内訳              ctr24 icr)
                              >> liftIO (f価格変換_事業所別生産物別売上高 24 ctr24 icr)
                              >> yield icr
                              >> f価格変換 24


-- | 消費税率
type ConsumeTaxRate = Double


-- ** H総売上，H事業別売上高
-----------------------------------------------------------
{- | H総売上，H事業別売上高
    *「金融，保険業，政治・経済・文化団体，宗教団体の活動，不動産事業」
    を除いた事業の売上には，売上（収入）金額×税率を足す．

    *すべての売り上げが消費税の課税対象であるわけではないので，
    事業別売上（収入）金額が未記入の場合は，
    売上（収入）金額×税率を加算．
    事業別売上（収入）金額が記入されていて且つ
    その総和が売上（収入）金額より大きい場合は，
    消費税加算後事業別売上（収入）金額の和で入れ替える．
-}

f価格変換_事業別売上高 :: ConsumeTaxRate -> IOCensusRow -> IO ()
f価格変換_事業別売上高 ctr icr
    =   readArray icr H消費税記入の別 >>= \taxBool
    ->  case taxBool of
            Null        -> return ()
            VBool False -> return ()
            VBool True  -> readArray icr H事業別売上高   >>= \sev
                        -> let addedSev = f事業別売上高税加算 ctr sev
                        in writeArray icr H事業別売上高 addedSev

-- | 税率を乗じる
f事業別売上高税加算 :: ConsumeTaxRate -> Val事業別売上高 -> Val事業別売上高
f事業別売上高税加算 ctr Null         = Null
f事業別売上高税加算 ctr (VCars cs)   = VCars $ V.map (multipleCar ctr) cs
    where
    multipleCar ctr car | shouldConvert car = car {value = (value car) * ctr}
                        | otherwise         = car

    -- 金融，保険業，政治・経済・文化団体，宗教団体の活動，不動産事業 ではないことの判定
    shouldConvert :: Car -> Bool
    shouldConvert tx = not $ L.elem (name tx) $ L.map T.pack ["T10","T11","T13"]

-- | 総売上に消費税を加算
f価格変換_総売上 :: ConsumeTaxRate -> IOCensusRow -> IO ()
f価格変換_総売上 ctr icr
    = readArray icr H消費税記入の別 >>= \taxBool
    ->  case taxBool of
            Null            -> return ()
            VBool False     -> return ()
            VBool True      -> readArray  icr H総売上   >>= \sales
                            -> case sales of
                                Null       -> return ()
                                VDouble bl -> writeArray icr H総売上 (VDouble (bl * ctr))

-- ** H費用等の内訳
-----------------------------------------------------------
{- | H費用等の内訳

![費用等の消費税加算処理図](consumeTaxCoset.png)

（「統計調査における売上高等の集計に係る消費税の取り扱いに関するガイドライン
平成24年経済センサス-活動調査をモデルとした消費税加算処理（調査品目以外）」より，抜粋（一部筆者編集）

-}

f価格変換_費用等の内訳 ::  ConsumeTaxRate -> IOCensusRow -> IO ()
f価格変換_費用等の内訳 ctr icr
    = readArray icr H消費税記入の別 >>= \taxBool
    ->   case taxBool of
            Null        -> return ()
            VBool False -> return ()
            VBool True  -> readArray icr H費用等の内訳   >>= \costsDetail
                        -> readArray icr H産業格付       >>= \kind
                        -> let newCost = f費用等の内訳税加算 (isCommerce kind) ctr costsDetail
                        in writeArray icr H費用等の内訳 newCost

    where
    isCommerce :: Val産業格付 -> Bool
    isCommerce Null = False
    isCommerce kind =  let lClass = (_大分類 ._産業格付) kind
                    in (lClass == T.pack "T4" || lClass == T.pack "T5" )

f費用等の内訳税加算 :: IsCommerce -> ConsumeTaxRate -> Val費用等の内訳 -> Val費用等の内訳
f費用等の内訳税加算 bl ctr Null      = Null
f費用等の内訳税加算 bl ctr (VCars cs) = runST $ do
                                stResult  <- newSTRef []
                                stTotal   <- newSTRef 0  :: ST s (STRef s Double) -- 費用総額
                                stSCost   <- newSTRef 0  :: ST s (STRef s Double) -- 売上原価
                                stToMinus <- newSTRef 0  :: ST s (STRef s Double)
                                V.forM_ cs (f費用別処理 stResult stTotal stSCost stToMinus ctr)

                                result    <- readSTRef stResult
                                total     <- readSTRef stTotal
                                sCost     <- readSTRef stSCost
                                toMinus   <- readSTRef stToMinus
                                stAdded   <- newSTRef 0

                                case (total /= 0, bl) of
                                    (True,  False)  -> let added = (sCost - (sCost/total) * toMinus) * (ctr - 1.0) -- 3 - {3/2 * (4 + 5 + 8)} * 税率
                                                    in case added < 0 of
                                                        True    -> writeSTRef stSCost sCost
                                                        False   -> writeSTRef stSCost (sCost + added)
                                                                >> writeSTRef stAdded added

                                    (_,     True )  -> writeSTRef stSCost (sCost * ctr)
                                                    >> writeSTRef stAdded (sCost * (ctr - 1.0))

                                    (False, _    )  -> writeSTRef stSCost (sCost * ctr)
                                                    >> writeSTRef stAdded (sCost * (ctr - 1.0))
                                resultSCost <- readSTRef stSCost
                                added       <- readSTRef stAdded
                                let sCostCar = (flip Car) (T.pack "売上原価") resultSCost
                                let totalCar = (flip Car) (T.pack "費用総額") (total + ((total - toMinus) * (ctr - 1.0)) + added)
                                return $ VCars $ V.fromList $ sCostCar : totalCar : result


f費用別処理 :: STRef s [Car] -> STRef s Double -> STRef s Double ->  STRef s Double ->  ConsumeTaxRate -> Car ->  ST s ()
f費用別処理 result total sCost toMinus ctr ca
    | name ca == T.pack "租税公課"         =  modifySTRef result (ca:)
                                           >> modifySTRef total   (value ca +)
                                           >> modifySTRef toMinus (value ca +)

    | name ca == T.pack "給与総額"         =  modifySTRef result (ca:)
                                           >> modifySTRef toMinus (value ca +)

    | name ca == T.pack "福利厚生費"       =  modifySTRef result (ca:)
                                           >> modifySTRef total (value ca +)
                                           >> modifySTRef toMinus (value ca +)

    | name ca == T.pack "支払利息"         =  modifySTRef result (ca:)
                                           >> modifySTRef total (value ca +)

    | name ca == T.pack "地代家賃"         =  modifySTRef result ((multipleValueCar ctr ca):)
                                           >> modifySTRef total (value ca +)

    | name ca == T.pack "減価償却費"       =  modifySTRef result ((multipleValueCar ctr ca):)
                                           >> modifySTRef total (value ca +)

    | name ca == T.pack "動産不動産賃借料" =  modifySTRef result ((multipleValueCar ctr ca):)
                                           >> modifySTRef total (value ca +)

    | name ca == T.pack "地代家賃"         =  modifySTRef result ((multipleValueCar ctr ca):)
                                           >> modifySTRef total (value ca +)

    | name ca == T.pack "売上原価"         =  writeSTRef sCost (value ca)
                                           >> modifySTRef total (value ca +)

    | name ca == T.pack "費用総額"         =  return ()
    | otherwise                            =  return ()




-- ** 事業所別生産物別売上高
-----------------------------------------------------------
{- |
    * 調査品目別の消費税の加算処理は，課税，直接輸出，の有無などによって以下の３パターンに区分される．

    ① 加算１（製造業の一部の品目）

        > 加算額 ＝（調査品目別売上-調査品目別直接輸出額）×税率

    ② 加算２（「医療，福祉」及び「サービス関連産業B」調査票の一部の品目）

        > 加算額＝（調査品目別売上-調査品目別海外取引額）×税率

    ③ 加算３

        > 加算額＝調査品目別売上×税率

    * 製造業における製造品出荷額
    > 加算額＝調査品目別消費税の加算処理における各製造品の加算額の合計

    * 製造業は，"H輸入割合"，サービス業は，"H相手先別収入割合_サB"および"H相手先別収入割合_医療福祉"で判定
    * 簡単のため製造業及び,医療福祉,サービス関連産業B は全て直接輸出ありとして扱う
-}

f価格変換_事業所別生産物別売上高 ::  Year -> ConsumeTaxRate -> IOCensusRow -> IO ()
f価格変換_事業所別生産物別売上高 year ctr icr
    = readArray icr H消費税記入の別 >>= \taxBool
    ->   case taxBool of
            Null        -> return ()
            VBool False -> return ()
            VBool True  -> readArray icr H事業所別生産物別売上高     >>= \valTar
                        -> readArray icr H輸出割合                   >>= \valEx
                        -> readArray icr H相手先別収入割合_サB       >>= \valSB
                        -> readArray icr H相手先別収入割合_医療福祉  >>= \valMed
                        -> f事業所別生産物別売上高税加算処理 year icr ctr valTar valEx valSB valMed

-- | 輸出割合
type ExportRate = Double


-- Nullのときの処理は,輸出入なしとして扱う( 修正案 :平均等)
f事業所別生産物別売上高税加算処理   :: Year
                                    -> IOCensusRow
                                    -> ConsumeTaxRate
                                    -> Val事業所別生産物別売上高
                                    -> Val輸出割合
                                    -> Val相手先別収入割合_サB
                                    -> Val相手先別収入割合
                                    -> IO ()
f事業所別生産物別売上高税加算処理 year icr ctr Null         valEx valSB valMed = return ()
f事業所別生産物別売上高税加算処理 year icr ctr (VCars tar)  valEx valSB valMed
    = let result = VCars (V.map (f生産物税加算 year ctr valEx valSB valMed ) tar)
    in writeArray icr H事業所別生産物別売上高 result

f生産物税加算   :: Year
                -> ConsumeTaxRate
                -> Val輸出割合
                -> Val相手先別収入割合_サB
                -> Val相手先別収入割合_医療福祉
                -> Car
                -> Car

f生産物税加算 24 ctr ex sb med ca
    | is製造業 24 ca = f加算1 ctr ex  ca
    | isサB    24 ca = f加算2 ctr sb  ca
    | is医療   24 ca = f加算2 ctr med ca
    | otherwise      = f加算3 ctr ca

f加算1 :: ConsumeTaxRate -> Val輸出割合 -> Car -> Car
f加算1 ctr Null         (Car v n) = Car v n
f加算1 ctr (VDouble ex) (Car v n) | v == 0    = (Car v n)
                                  | otherwise = Car (v + (v - (v * ex * 0.01)) * (ctr - 1)) n

f加算2 :: ConsumeTaxRate -> Val相手先別収入割合 -> Car -> Car
f加算2 ctr Null                   (Car v n) = Car v n
f加算2 ctr (V相手先別収入割合 ex) (Car v n) = Car (v + (v - (v * (_海外取引 ex) * 0.01) * (ctr - 1))) n


f加算3 :: ConsumeTaxRate -> Car -> Car
f加算3 ctr (Car v n) = Car (v * ctr) n

-- | サBかどうかを判定
isサB :: Year -> Car -> Bool
isサB 24 ca | T.take 2 (name ca) == T.pack "39"                                       = True
            | T.take 2 (name ca) == T.pack "40"                                       = True
            | T.take 2 (name ca) >= T.pack "83" &&  T.take 2 (name ca) >= T.pack "85" = True
            | T.take 2 (name ca) == T.pack "95"                                       = True
            | otherwise                                                               = False

-- | 医療かどうかを判定
is医療 :: Year -> Car -> Bool
is医療 24 ca | name ca             == T.pack "PZZZ"                                    = True
             | T.take 2 (name ca) >= T.pack "68" &&  T.take 2 (name ca) >= T.pack "92" = True
             | otherwise                                                               = False

-- | 製造業かどうかを判定
is製造業 :: Year -> Car -> Bool
is製造業 24 ca  | T.take 2 (name ca) == T.pack "09"                                       = True
                | T.take 2 (name ca) >= T.pack "10" &&  T.take 2 (name ca) >= T.pack "32" = True
                | otherwise                                                               = False

-----------------------------------------------------------
-- * 名寄せ
-----------------------------------------------------------

type EnDivideMap = Map (E直轄企業コード,Header) Double


{- |

    V表の作成において必要な項目は，平成24年センサスにおける「企業全体の売上（収入）金額，
     費用総額及び費用内訳」（売上高未把握事業所の補定，VAT推計及びマージン額推計に利用），
     「商品売上原価」，「年初及び年末商品手持額」，「年間商品仕入れ額」（マージン推計に利用）の３項目．

    補定は既に行われているので,ここでは,マージン推計用に
    「商品売上原価，年初及び年末商品手持額，年間商品仕入れ額｣と，直轄企業コードのマップを作成する．

    商業の企業調査票の場合のみ

-}

f名寄せ :: (MonadIO m) => IORef EnDivideMap -> ConduitT IOCensusRow Void m EnDivideMap
f名寄せ edm =  await >>= \ maybeIcd
            -> case maybeIcd of
                Nothing  -> (liftIO . readIORef) edm
                Just icd -> liftIO (readArray icd H調査票の種類) >>= \ kind
                         -> case (isEN kind) of
                                 (Just True) -> liftIO $ f商業企業項目取得 icd edm
                                 _           -> liftIO $ return ()
                         >> f名寄せ edm


-- | 企業または，団体かを判断する
--   Nothing の時は除外

{-# INLINE isEN #-}
isEN :: Val調査票の種類 -> Maybe Bool
isEN Null                                                                        = Nothing
isEN (V調査票の種類 (E調査票の種類 kind target subject))
    | (kind == E企業調査票) || (kind == E団体調査票) || (subject == E団体法人用) = Just True
    | otherwise                                                                  = Just False


f商業企業項目取得 :: IOCensusRow -> IORef EnDivideMap -> IO ()
f商業企業項目取得 icd edm   = readArray icd H直轄企業コード >>= \ link
                            -> case link of
                                Null      -> return ()
                                VText tx  -> let top = (T.init . T.init) tx
                                          in forM_ [H商品売上原価, H年間仕入額,H年初商品手持額,H年末商品手持額] $ \h
                                                -> readArray icd h >>= \ tmpVal
                                                -> case tmpVal of
                                                        Null       -> return ()
                                                        VDouble x  -> modifyIORef' edm (Map.insert (top,h) x)

{-# INLINE getDoubleFromVal #-}
getDoubleFromVal :: ValDouble -> Double
getDoubleFromVal Null          = 0
getDoubleFromVal (VDouble dl)  = dl

-----------------------------------------------------------
-- * 企業の事業所への分割
-----------------------------------------------------------

-- | ファイルを受け取って企業の事業所への分割をする.
full企業分割 :: InputFile -> Double -> Year -> IO ()
full企業分割 inputFile maxRowNum year
    =   getWeightAndLink inputFile >>= \ (iwm, edm)
    ->  newIORef Map.empty         >>= \empDenomiMap
    ->  runConduitRes (sourceCensus  inputFile  .| getDenomiMap iwm empDenomiMap) >>= \denomi
    ->  runConduitRes $ sourceCensus inputFile  .| f企業分割 iwm edm denomi  .| sinkCensus maxRowNum outputFile
    where outputFile = (((init. init . init . init) inputFile) ++ "Divide.csv")


{- |第12回産業連関技術会議資料 における（組替）集計上の留意事項の一つに，
    「企業調査票にしかデータがない項目（設備投資，費用に係る項目など）については，
    事業所別従業者数等で案分して，可能な限り，事業所別データに変換してから組替集計を実施」
    「ただし，複数事業所を有する企業であって，ネットワーク型産業に該当するものについては，
    売上高及び費用共に事業所票で把握されないことから，企業調査票のデータを利用」との記載がある．

     V表の作成において必要な項目は，平成24年センサスにおける「企業全体の売上（収入）金額，
     費用総額及び費用内訳」（売上高未把握事業所の補定，VAT推計及びマージン額推計に利用），
     「商品売上原価」，「年初及び年末商品手持額」，「年間商品仕入れ額」（マージン推計に利用）の３項目．

    補定は既に行われているので,ここでは,マージン推計用に
    「商品売上原価，年初及び年末商品手持額，年間商品仕入れ額｣のみ分割する.

     その具体的な手法に関しては，筆者の調べる限り資料が存在しないが，
     平成28年経済センサスにおける売上（収入）に関する試算がHP「（参考）全産業の事業所の売上（収入）金額に関する試算値」
     において説明されている．

    \(X[v],x_i [v]\)がそれぞれ，企業のvの値，企業傘下事業所の内整理番号iのvの値を表すとし，
    ある企業に属すべての事業所の整理番号をIとする．Iのうち，分割対象に属する部分をIN,それいがいをOUTとする．
    また，ある事業所iの主業の産業別ウェイトをweight[i]とすると，企業から分割された事業所の値は，

    \[  x_i= (X[v] - \sum_{j \in OUT} x_j [v]) \times \frac{x_i [w] \times weight[i]}{\sum_{i \in I}{x_i [w] \times weight[i]}} \]

    となる．なお，産業別ウェイトは，産業大分類ごとに，主産業に格付けされた事業所の事業従事者数の合計が，
    企業全体の事業従事者数の70%以上となる企業（単一産業企業）全体の売上高を，当該企業全体の事業従業者数で除して求める．

    ここで，「商品売上原価，年初及び年末商品手持額，年間商品仕入れ額｣は商業を行っていない事業所では発生しないため

    \[ \sum_{j \in OUT} x_j [v] = 0 \]

    であるから

    \[  x_i= X[v] \times \frac{x_i [w] \times weight[i]}{\sum_{i \in I}{x_i [w] \times weight[i]}} \]

    が成り立つ．

-}


f企業分割 :: (MonadIO  m) => IndWeightMap ->  EnDivideMap ->  DenomiMap -> ConduitT IOCensusRow IOCensusRow m ()
f企業分割 iwm edm dm = do
        maybeIcd <- await
        case maybeIcd of
            Nothing  -> liftIO (putStrLn "end 企業分割") >> return ()
            Just icd -> do
                valLink  <- liftIO $ readArray icd  H直轄企業コード
                valEmp   <- liftIO $ readArray icd  H雇用情報
                valClass <- liftIO $ readArray icd  H産業格付
                liftIO ( forM_ [H商品売上原価, H年間仕入額,H年初商品手持額,H年末商品手持額] ( \h
                            -> culc icd iwm edm dm valLink valClass valEmp h))
                yield icd
                f企業分割 iwm edm dm
    where
    culc ::  IOCensusRow -> IndWeightMap -> EnDivideMap -> DenomiMap -> Val直轄企業コード -> Val産業格付 -> Val雇用情報 -> Header -> IO ()
    culc icd iwm edm dm valLink valKind valEmp h = case (valEmp,valKind,valLink) of
        (V雇用情報 emp, V産業格付 kind, VText tx)  -> let worker = fromIntegral (_事事業従業者数 emp)
                                                    in let lInd = _大分類 kind
                                                    in let top  = (T.init . T.init ) tx
                                                    in ifNotNull icd iwm edm dm top lInd worker h
        _                                           -> return ()

    ifNotNull ::  IOCensusRow -> IndWeightMap -> EnDivideMap -> DenomiMap -> E直轄企業コード -> Industry -> Double -> Header -> IO ()
    ifNotNull icr iwm edm dm top lInd worker h = case (Map.lookup (lInd,h) iwm, Map.lookup (top,h) edm, Map.lookup (top, h) dm ) of
        (Just weight, Just enV, Just denomi)    -> case (denomi /= 0) of
                                                    True  -> writeArray icr h (VDouble ( enV * (worker * weight) / denomi ))
                                                    False -> return ()
        _                                       -> return ()


-- | 産業別ウェイトと，名寄せを同時に行う
getWeightAndLink :: InputFile -> IO (IndWeightMap, EnDivideMap)
getWeightAndLink input  =  newIORef Map.empty >>= \ empMap1
                        -> newIORef Map.empty >>= \ empMap2
                        -> runConduitRes
                        $  sourceCensus input
                        .| getZipSink ((,)  <$> ZipSink (f産業別ウェイト取得 empMap1) <*> ZipSink (f名寄せ empMap2))


-- | 直轄企業コードの下２桁意外と，分母 [\ \sum_{i ∈ I}{x_i [w]× weight[i]} \] のMap
type DenomiMap = Map (E直轄企業コード, Header) Double


-- | 企業別の分母 [\ \sum_{i ∈ I}{x_i [w]× weight[i]} \] を求める
getDenomiMap :: (MonadIO m) => IndWeightMap -> IORef DenomiMap -> ConduitT IOCensusRow Void m DenomiMap
getDenomiMap iwm dmp = do
        maybeIcd <- await
        tmpMap   <- liftIO (newIORef Map.empty)
        -----------------------------------------------------------
        case maybeIcd of
            Nothing   -> liftIO (readIORef dmp) >>= return
            Just icd  -> do
                valLink  <- liftIO (readArray icd H直轄企業コード)
                valType  <- liftIO (readArray icd H調査票の種類)
                valEmp   <- liftIO (readArray icd H雇用情報)
                valKind  <- liftIO (readArray icd H産業格付)
                -----------------------------------------------------------
                case isEN valType of
                    Just False -> liftIO (ifNotEn tmpMap valLink valEmp valKind) >> getDenomiMap iwm dmp
                    _          -> getDenomiMap iwm dmp

    where
    ifNotEn :: IORef DenomiMap -> Val直轄企業コード -> Val雇用情報 -> Val産業格付 -> IO ()
    ifNotEn tmpMap valLink valEmp valKind = case valLink of
        Null        -> return ()
        VText link  -> let top = (T.init . T.init) link
            in readIORef tmpMap >>= \ redMap
            -> forM_ [H商品売上原価, H年間仕入額,H年初商品手持額,H年末商品手持額] $ \h
                -> case Map.lookup (top,h) redMap of
                        Nothing   -> modifyPart h valKind iwm tmpMap valEmp top 0
                        Just num  -> modifyPart h valKind iwm tmpMap valEmp top num

    modifyPart :: Header -> Val産業格付 -> IndWeightMap -> IORef DenomiMap -> Val雇用情報 -> Industry ->  Double -> IO ()
    modifyPart h valKind iwm tmpMap valEmp top num  = case valKind of
        Null                -> return ()
        V産業格付 kind      -> let lInd = _大分類 kind
                            in case Map.lookup (lInd,h) iwm  of
                            Nothing     -> return ()
                            Just weight -> modifyIORef' tmpMap (Map.insert (top,h) (num + ((getWorker valEmp) * weight)))

    -- | 事業従業者数をとる
    getWorker :: Val雇用情報 -> Double
    getWorker Null            = 0
    getWorker (V雇用情報 emp) = fromIntegral (_事事業従業者数 emp)


{- | 産業別ウェイト
    産業大分類ごとに，主産業に格付けされた事業所の事業従事者数の合計が，
    企業全体の事業従事者数の70%以上となる企業（単一産業企業）全体の対象の値を，当該企業全体の事業従業者数で除して求める

    大分類以下の細かい分類でこれを行ってもよい（要修正）

-}

type IndWeightMap  = Map (Industry,Header) Double



-- | 企業別の情報を集めたMap
type EnWeightInfoMap = Map E直轄企業コード EnWeightInfo


{- | 企業直轄企業コード，企業別主産業，全体売上高，全体事業従業者数，該当事業従業者数
    を記録するためのデータ型

-}
data EnWeightInfo = EWI { lInd      ::                Industry     -- ^ 企業の産業大分類
                        , enCost    :: {-# UNPACK #-} Double       -- ^ 企業の商品売上原価
                        , enBought  :: {-# UNPACK #-} Double       -- ^ 企業の年間仕入額
                        , enBegin   :: {-# UNPACK #-} Double       -- ^ 企業の年初商品手持額
                        , enEnd     :: {-# UNPACK #-} Double       -- ^ 企業の年末商品手持額
                        , totalEmp  :: {-# UNPACK #-} Int          -- ^ 企業の全体事業従業者数(分母)
                        , targetEmp :: {-# UNPACK #-} Int          -- ^ 該当事業従業者数 (分子)
                        }

getDataFromEWI :: Header -> (EnWeightInfo -> Double)
getDataFromEWI H商品売上原価   = enCost
getDataFromEWI H年間仕入額     = enBought
getDataFromEWI H年初商品手持額 = enBegin
getDataFromEWI H年末商品手持額 = enEnd


{- | Nothingになるまで STRefでEnWeightInfoを収集し，NothingでそれをEnWeightInfoMap に変換して返す

企業か，団体の場合は，全体の売上高を記入 売り上げがない場合は変換の段階で除外．
（ネットワーク産業でも，売上高のみ）

事業所の場合は，該当するなら直轄企業に該当事業従業者数及び，従業者数を記入


個人経営，単独事業所は，対象から除く

-}

f産業別ウェイト取得 ::(MonadIO m) => IORef EnWeightInfoMap -> ConduitT IOCensusRow Void m IndWeightMap
f産業別ウェイト取得 imap   = do
        maybeIcd  <- await
        case maybeIcd of
            Nothing  ->  liftIO (readIORef imap)
                     >>= return . makeIndWeightMap

            Just icd -> do

                !kind   <- liftIO (readArray icd H調査票の種類    )
                !triple <- liftIO (readArray icd H単独本所支所区分)

                case (isEN kind, isSingle kind triple) of
                    (Nothing,    True)  -> liftIO (whenIsSi icd imap)
                    (Nothing,    False) -> liftIO (whenIsES icd imap)
                    (Just True,  True)  -> liftIO (whenIsSi icd imap)
                    (Just True,  False) -> liftIO (whenIsEN icd imap)
                    (Just False, True)  -> liftIO (whenIsSi icd imap)
                    (Just False, False) -> liftIO (whenIsES icd imap)

                f産業別ウェイト取得 imap

{-# INLINE whenIsEN #-}
whenIsEN :: IOCensusRow ->  IORef EnWeightInfoMap ->  IO ()
whenIsEN icd smap = do
        tmpMap <- readIORef smap
        valCode   <- liftIO (readArray icd H直轄企業コード)
        case valCode of
            Null           -> return ()
            (VText code)   -> do
                let top = (T.init .T.init) code

                case Map.lookup top tmpMap of
                    Nothing  -> do
                        valInd   <- liftIO (readArray icd H産業格付)
                        cost   <- getDoubleFromVal <$> (readArray icd H商品売上原価)
                        bought <- getDoubleFromVal <$> (readArray icd H年間仕入額)
                        begin  <- getDoubleFromVal <$> (readArray icd H年初商品手持額)
                        end    <- getDoubleFromVal <$> (readArray icd H年末商品手持額)
                        case valInd of
                            V産業格付 ind  -> modifyIORef' smap (Map.insert top (EWI (_大分類 ind) cost bought begin end 0 0))
                            _              -> return ()

                    Just ewi ->  do
                        valInd   <- liftIO (readArray icd H産業格付)
                        cost   <- getDoubleFromVal <$> (readArray icd H商品売上原価)
                        bought <- getDoubleFromVal <$> (readArray icd H年間仕入額)
                        begin  <- getDoubleFromVal <$> (readArray icd H年初商品手持額)
                        end    <- getDoubleFromVal <$> (readArray icd H年末商品手持額)
                        case valInd of
                            V産業格付 ind -> do
                                    let  tmpIndustry  = lInd      ewi
                                    let  tmpTotalEmp  = totalEmp  ewi
                                    let  tmpTargetEmp = targetEmp ewi
                                    let  tmpEwi       = EWI tmpIndustry cost bought begin end tmpTotalEmp tmpTargetEmp
                                    modifyIORef' smap (Map.insert top tmpEwi)
                            _             -> return ()
{-# INLINE whenIsES #-}
whenIsES :: IOCensusRow ->  IORef EnWeightInfoMap ->  IO ()
whenIsES icd smap = do
        tmpMap    <- readIORef smap
        valCode   <- liftIO (readArray icd H直轄企業コード)
        case valCode of
            Null           -> return ()
            (VText code)   -> do
                let top = (T.init .T.init) code

                case (Map.lookup top tmpMap) of
                    Nothing  -> do
                        valInd <- liftIO (readArray icd H産業格付)
                        valEmp <- liftIO (readArray icd H雇用情報)

                        case  (valInd, valEmp) of
                            (V産業格付 ind, V雇用情報 emp)-> do
                                let totalEmpToAdd  =  _事雇用者数 emp
                                let targetEmpToAdd =  _事事業従業者数 emp
                                let tmpEwi         = EWI (_大分類 ind) 0 0 0 0 totalEmpToAdd targetEmpToAdd
                                modifyIORef' smap (Map.insert top tmpEwi)
                            (_,               _) -> return ()

                    Just ewi ->  do
                        valInd <- liftIO (readArray icd H産業格付)
                        valEmp <- liftIO (readArray icd H雇用情報)

                        case  (valInd, valEmp) of
                            (V産業格付 ind, V雇用情報 emp)-> do
                                let totalEmpToAdd  =  _事雇用者数 emp
                                let targetEmpToAdd =  _事事業従業者数 emp
                                if (lInd ewi == (_大分類 ind))
                                    then modifyIORef' smap (Map.insert top (ewi {totalEmp  = (totalEmp  ewi) + totalEmpToAdd} ))
                                    else modifyIORef' smap (Map.insert top (ewi {totalEmp  = (totalEmp  ewi) + totalEmpToAdd
                                                                                ,targetEmp = (targetEmp ewi) + targetEmpToAdd} ))
                            _   -> return ()
{-# INLINE whenIsSi #-}
whenIsSi :: IOCensusRow ->  IORef EnWeightInfoMap ->  IO ()
whenIsSi icd smap = return ()

makeIndWeightMap :: EnWeightInfoMap ->  IndWeightMap
makeIndWeightMap xs =  runST $ do
                tmpMap <- newSTRef Map.empty
                forM_ ys $ \y -> do
                    forM_ [H商品売上原価, H年間仕入額, H年初商品手持額, H年末商品手持額] $ \h -> do

                        redMap <- readSTRef tmpMap
                        case Map.lookup (lInd y, h) redMap of
                            Nothing  ->
                                when ((getDataFromEWI h) y /= 0 )(
                                     modifySTRef tmpMap (Map.insert (lInd y,h) (((getDataFromEWI h) y), (targetEmp y))))

                            Just tup -> do
                                when ((getDataFromEWI h) y /= 0 )(
                                     modifySTRef tmpMap (Map.insert (lInd y,h)  ( fst tup + (getDataFromEWI h) y
                                                                                , snd tup + targetEmp y )))
                resultMap <- readSTRef tmpMap
                return $ Map.map (\x -> if snd x /= 0 then  (fst x) / ((fromIntegral . snd) x) else 1) resultMap
    where
    ~ys  =  Map.elems
        $! Map.filter
        (\x  ->  (((fromIntegral . totalEmp) x)  /= 0) && (((fromIntegral . targetEmp) x) / ((fromIntegral . totalEmp) x) >= 0.7)) xs



-- | 個人経営者,あるいは単独事業所か否かを判定する
{-# INLINE isSingle #-}
isSingle :: Val調査票の種類 -> Val単独本所支所区分 -> Bool
isSingle Null Null = True
isSingle (V調査票の種類 (E調査票の種類 kind target subject)) Null
    = ((kind == E単独事業所調査票 || kind ==  E個人経営調査票) || (subject == E個人経営者用))
isSingle (V調査票の種類 (E調査票の種類 kind target subject)) (V単独本所支所区分 triple)
    = ((kind == E単独事業所調査票 || kind ==  E個人経営調査票) || (subject == E個人経営者用)) || (triple == E単独事業所)
isSingle Null (V単独本所支所区分 triple)
    = (triple == E単独事業所)


-----------------------------------------------------------
-- * マージン推計
-----------------------------------------------------------

-- | ファイルを受け取って


{- | 商業マージン推計

    JSNAにおけるV表は国連基準である，基本価格表示とは異なり，運輸・商業マージンをそれぞれの産業の自交点に計上している．
    SUT体系への移行後のS表においてどのような価格を採用するかは現行未定であるので，
    本稿では現行V表に合わせて，推計されたマージンはそれぞれの自交点に計上する．
    以降各マージンの推計手法に関して外観，考察する．

     平成23年V表における各産業の総生産額は平成23年産業連関表取引基本表の行和が用いられている．
     平成23年産業連関表総合解説編 によれば，産業連関表における商業マージンは

     「商業マージン＝売上額（商業販売額）－ 仕入額」

     によって定義されており，平成23年表では「経済センサス-活動調査」の組替集計結果（部内資料）より推計されている．

     一方，第52回サービス統計・企業統計部会配布資料 では，
     平成24年における商業マージン額の推計手法は，商品販売額から企業調査票等の調査項目である商品売上原価を引く形で求めていると説明している．

    平成24年センサス商業マージン額（主業，従業）=年間商品販売額-商品売上原価

    また，平成28年経済センサスにおいては調査委項目に年初商品手持額が追加され，
    他の記入項目から計算が可能であるため，売上原価に対する調査項目が廃止され，
    また平成24年センサスにおいて，商業マージンの大半を主業が占めていたことから従業に関する売上原価の把握を取りやめ，
    以下のように推計すると説明されている．

    平成２8年センサス商業マージン額（主業）＝年間商品販売額- （年初商品手持額＋年間商品仕入額-年末商品手持額）

     以下基本的には上記資料に従い，それぞれの項目が取得できない場合における場合を考慮して，
     平成24年，平成28年それぞれの商業マージン推計手法を設計する．

     商業マージンの推計に用いる項目は，

    ・平成24年企業調査票における①「商品売上原価」

    ・平成28年経済センサス企業調査票における②「年初及び年末商品手持額」，③「年間商品仕入額」

    ・平成24年，28年単独事業所調査票及び，事業所調査票（卸売業，小売業）における調査項目④「年間商品販売額」，
    ⑤「費用総額及び費用内訳」のうち「売上原価」

    ・その他調査票における⑥「事業別売上（収入）金額」のうち卸売業，小売業の回答額

    となる．各項目の調査票別の有無は，「表 2 各年度別調査票に含まれるマージン推計に利用される項目とマージン推計手法」にまとめた．
    以降，未回答の場合を含めて，各情報の記載の有無にそって「図 7 商業マージン取得ワークフロー」に従って商業マージンを求める．


    ![商業マージン取得ワークフロー図](margin.png)

    処理としては，２２区分の売上高の値及び事業所別生産物別売上高のうち商業に該当するものに処理を施していく．
    類似調査票処理が必要になったものは IORef [IOCensusRow] で保存し，終了後すべて処理してyieldする．

    本当は自家倉庫や管理補助的業務分にはマージン率を乗じるべきではない(未対応)

    同一産業処理は,必要な場合Listにためておき,最後にまとめて処理を行う.
-}


f商業マージン処理 :: (Monad m, MonadIO m) =>  IORef ToMakeMarginMap -> IORef [IOCensusRow] ->  ConduitT IOCensusRow IOCensusRow m ()
f商業マージン処理  refTmm icrList = do
        maybeIcr <- await
        case maybeIcr of
            Nothing     -> liftIO (readIORef icrList) >>= \ !ls
                        -> liftIO (readIORef refTmm)  >>= \ !tm
                        -> liftIO (putStrLn "start f同一産業処理")
                        >> CL.sourceList ls .| f同一産業処理 (makeMarginMap tm)

            Just icr    -> liftIO (readArray icr H事業別売上高)           >>= \ !valSev
                        -> liftIO (readArray icr H商品売上原価)           >>= \ !valCost
                        -> liftIO (readArray icr H事業所別生産物別売上高) >>= \ !valTar
                        -> liftIO (readArray icr H年初商品手持額)         >>= \ !valBegin
                        -> liftIO (readArray icr H年末商品手持額)         >>= \ !valEnd
                        -> liftIO (readArray icr H年間仕入額)             >>= \ !valBought
                        -> liftIO (readArray icr H産業格付)               >>= \ !valKind
                        -> (case (valSev,valCost,valBegin,valEnd,valBought) of
                            (Null,_,_,_,_)
                                -> liftIO (modifyIORef' icrList (icr:))

                            (VCars sev, VDouble cost,_,_,_)
                                -> let cSales = (V.sum . (V.map value) . (V.filter isCommerceDetail)) sev
                                in case (cSales /= 0) of
                                     True -> let !mr = (cSales - cost) / cSales
                                          in case ((mr <= 1) && (mr > 0)) of
                                                False   -> yield icr
                                                True    -> liftIO (f表面裏面処理 mr icr valSev valTar valKind refTmm)
                                                        >> yield icr
                                     False -> liftIO (modifyIORef' icrList (icr:))

                            (VCars sev, Null, VDouble begin, VDouble end, VDouble bought)
                                -> let !cSales = (V.sum . (V.map value) .(V.filter isCommerceDetail)) sev
                                in let !mr = cSales - begin + end - bought
                                in case ((mr <= 1) && (mr > 0)) of
                                    False   -> yield icr
                                    True    -> liftIO (f表面裏面処理 mr icr valSev valTar valKind refTmm)
                                            >> yield icr

                            (VCars sev, Null, _, _, _)
                                -> liftIO (modifyIORef' icrList (icr:)))

                        >> f商業マージン処理  refTmm icrList

-- | マージン率
type MarginRate = Double

-- | 同一の大分類に格付けされている事業所の平均マージン率
type MarginMap  = Map Industry MarginRate

-- | MarginMapを作るための中間データ型
type ToMakeMarginMap = Map Industry (MarginRate, Double)


makeMarginMap :: ToMakeMarginMap -> MarginMap
makeMarginMap mm = Map.map (\(x,y) -> if y /= 0 then x / y else 1) mm


-- | 事業分類の商業及び,裏面の商業をマージン化する
{-# INLINE f同一産業処理 #-}
f同一産業処理 :: (MonadIO m) => MarginMap -> ConduitT IOCensusRow IOCensusRow m ()
f同一産業処理 mm = do
    maybeIcr <- await
    case maybeIcr of
        Nothing  -> return ()
        Just icr -> liftIO ( f icr ) >> yield icr >> f同一産業処理 mm
    where
    f :: IOCensusRow -> IO ()
    f icr    = readArray icr H事業別売上高           >>= \ !sev
            -> readArray icr H事業所別生産物別売上高 >>= \ !tar
            -> readArray icr H産業格付               >>= \ !kind
            -> case kind of
                V産業格付 (E産業格付 l o m s t d)
                        | Maybe.isJust (Map.lookup l mm)
                            ->  let Just mr = (Map.lookup l mm)
                            in writeArray icr H事業別売上高           (convMarginSev  mr sev)
                            >> writeArray icr H事業所別生産物別売上高 (convMarginComm mr tar)
                        | otherwise
                            -> writeArray icr H事業別売上高           (convMarginSev  (mm2mr mm) sev)
                            >> writeArray icr H事業所別生産物別売上高 (convMarginComm (mm2mr mm) tar)

    -- | 産業分類がわからないとき用に,全体の平均のマージン率を用いる
    {-# INLINE mm2mr #-}
    mm2mr :: MarginMap -> Double
    mm2mr mm  | Map.size mm /= 0 = ((L.sum . Map.elems) mm) / ((fromIntegral . Map.size) mm)
              | otherwise        = 1.0 -- error "Error: mm2MR, in module V; MarginMap is empty" ここの処理も要注意

-- | 商業のみ事業別売上高(細分類)マージン率を乗じる

{-# INLINE convMarginSev #-}
convMarginSev :: MarginRate -> Val事業別売上高 -> Val事業別売上高
convMarginSev mr (VCars cs) = case ((mr <= 1) && (mr > 0)) of
                                    True  -> VCars  $ (flip V.map) cs
                                                    $ \x ->  if | (name x == "T5" || name x == "T4") -> x {value = (value x) * mr }
                                                                | otherwise                          -> x

                                    False -> VCars cs
convMarginSev mr x = x

-- | 商業のみ事業所別生産物別売上高(細分類)マージン率を乗じる
{-# INLINE convMarginComm #-}
convMarginComm :: MarginRate -> Val事業所別生産物別売上高 -> Val事業所別生産物別売上高
convMarginComm mr (VCars cs) = case ((mr <= 1) && (mr > 0)) of
                                    True  -> VCars $ (flip V.map) cs
                                                   $ \x ->  if | isCommerceDetail x -> x {value = (value x) * mr }
                                                               | otherwise          -> x
                                    False -> VCars cs
convMarginComm mr x = x


-- | 産業細分類の商業か否かを判定する
{-# INLINE isCommerceDetail #-}
isCommerceDetail :: Car -> Bool
isCommerceDetail ca | "51" <= T.take 1 (name ca) && T.take 1 (name ca)  <= "61"  = True
                    | name ca == "I1ZZ"                                          = True
                    | name ca == "I2ZZ"                                          = True
                    | otherwise                                                  = False

-- | 22区分のマージン率を生産物別別売上高に乗じる
{-# INLINE f表面裏面処理 #-}
f表面裏面処理 :: MarginRate
              -> IOCensusRow
              -> Val事業別売上高
              -> Val事業所別生産物別売上高
              -> Val産業格付
              -> IORef ToMakeMarginMap
              -> IO ()

f表面裏面処理 mr icr sev tar kind refTmm
    =  writeArray icr H事業別売上高           (convMarginSev  mr sev)
    >> writeArray icr H事業所別生産物別売上高 (convMarginComm mr tar)
    >> case kind of
        Null                                    -> return ()
        V産業格付 (E産業格付 l o m s t d)       -> readIORef refTmm >>= \tmm
                                                -> case Map.lookup l tmm of
                                                    Nothing     -> modifyIORef' refTmm (Map.insert l (mr,1))
                                                    Just (m,i)  -> modifyIORef' refTmm (Map.insert l (m + mr,i + 1))

-----------------------------------------------------------
-- * 重複の削除
-----------------------------------------------------------
-- ** 企業内取引及び下請け構造
------------------------------------------------------------------

{- |  企業内取引及び下請け構造

 第21回サービス統計・企業統計部会配布資料 では，
 「製造業の企業においては，部品工場から完成品組み立て工場への部品供給のように企業内取引が存在しているものと考えられる」とし，
 その取り扱いにおいて，企業調査票における売上額と，
 事業所調査票の売上額の差額を企業内取引として把握した上で経済センサスの集計の企業集計表においては，
 企業内取引を計上しない形で，事業所集計表においては企業内取引を計上する形で表象するという方針が掲げられている．
 したがって，事業所を集計単位とする製造業においては，現行の産業連関表において，企業内取引は生産額に集計されている．

 SNAにおけるソフトウェア業及び情報処理・提供サービスなどの生産額を推計するには，
 その売上高からOEM（相手先ブランド名製造）などによって重複する分の同業者間取引額及び同一企業間取引額を除外する必要がある。
 産業連関表におけるそのそれらの産業に取り扱いに関しては，「平成23年（2011年）産業連関表 総合解説編」においてソフトウェア業，
 情報処理・提供サービス ，広告 ，警備業，プラントエンジニアリング業及び鉱物探査以外のその他の対事業所サービス
 はいずれも経済センサス-活動調査を資料として「同業者間取引及び同一企業間取引額を除外して生産額を求めた」との記述がある．

 この内，同一企業間取引額に相当するのが企業内取引とみなされるものであり，
 上記の事業は全て経済センサスでは「サービス関連産業B」に関する調査票で調査されている．事業所調査票（サービス関連産業B）には，
 「サービス関連産業Bの相手先別収入割合」という項目が存在し，ソフトウェア業及び，
 情報利処理・提供サービスを除く事業に関しては，
 調査項目の内「同一企業間取引」によって把握された同一企業内取引額を事業所の売上高から除外する処理が行われている．
 ソフトウェ業及び，情報処理・提供サービス業においては，
 同調査票における調査項目「特定のサービス業における同業者との契約割合」に当たる売上高を除外する処理が行われているものと考えられる．
 また，「物品賃貸業（貸し自動車を除く．）」に関しても，特定サービス産業実態調査を利用して，
 受注した業務の外部委託と考えられる同業者間取引額を差し引いたとの記述があるが，
 経済センサスでは物品賃貸業に係る同業者間取引を把握できないことから，
 代替として「サービス関連産業Bの相手先別収入割合」における「同一企業内取引」分を除外することとする．

 2021年経済センサス以降，サービス関連産業Bが企業調査票となった場合，
 これらの処理の内企業内取引はそもそも調査票に現れなくなるため，処理が不必要となるが，
 現行の「相手先収入割合」及び「同業者との契約割合」によって推計される額と同等のものとなるかに関しては，議論が必要である．
-}

f企業内取引削除 :: (MonadIO m) => Year -> ConduitT IOCensusRow IOCensusRow m ()
f企業内取引削除 year =  await >>= \maybeIcr
                    -> case maybeIcr of
                        Nothing   -> return ()
                        Just icr  -> liftIO  ( readArray icr H相手先別収入割合_サB    >>= \ !valTarget
                                            -> readArray icr H同業者割合_サB          >>= \ !valSame
                                            -> readArray icr H事業別売上高            >>= \ !valBusi
                                            -> readArray icr H事業所別生産物別売上高  >>= \ !valComm
                                            -> f企業内取引削除処理 year icr valTarget valSame valBusi valComm)
                                  >> yield icr
                                  >> f企業内取引削除 year


{- | 事業所別生産物別売上高及び事業別売上高から企業内取引と同一企業間取引を削除する

値のないものの事業分類に関しては取引の削除を行わない(平均値使うとか要修正)

事業別売上高からは,生産物別売上高で引いた総額を引く
-}

f企業内取引削除処理     :: Year
                        -> IOCensusRow
                        -> Val相手先別収入割合_サB
                        -> Val同業者割合_サB
                        -> Val事業別売上高
                        -> Val事業所別生産物別売上高
                        -> IO ()

f企業内取引削除処理 year icr valTarget valSame valBusi valComm  = do
        toMinusInfo <- newIORef 0.0 -- 情報産業のマイナス分
        toMinusRent <- newIORef 0.0 -- 物品賃貸業のマイナス分
        toMinusOth  <- newIORef 0.0 -- 上記以外のサービス業のマイナス分
        --  事業所別生産物別売上高処理
        f情報産業削除    year icr toMinusInfo valSame   valComm
        f物品賃貸業削除  year icr toMinusRent valTarget valComm
        fその他のサB削除 year icr toMinusOth  valTarget valComm
        --  事業別売上高処理
        case valBusi of
            Null        -> return ()
            VCars busi  -> readIORef toMinusInfo >>= \minusInfo
                        -> readIORef toMinusRent >>= \minusRent
                        -> readIORef toMinusOth  >>= \minusOth
                        -> writeArray icr H事業別売上高 (VCars (V.map (f minusInfo minusRent minusOth) busi))

        where
        f minusInfo minusRent minusOth (Car v n)
            | n == "T12" = case (v - minusInfo) >= 0 of
                                True    -> Car (v - minusInfo) n
                                False   -> Car v n
            | n == "T14" = case (v - minusRent) >= 0 of
                                True    -> Car (v - minusRent) n
                                False   -> Car v n
            | n == "T20" = case (v - minusOth) >= 0 of
                                True    -> Car (v - minusOth)  n
                                False   -> Car v n
            | otherwise  = Car v n



f情報産業削除 :: Year -> IOCensusRow ->  IORef Double ->  Val同業者割合_サB -> Val事業所別生産物別売上高 ->  IO ()
f情報産業削除 year icr toMinusInfo Null           _             = return ()
f情報産業削除 year icr toMinusInfo _              Null          = return ()
f情報産業削除 year icr toMinusInfo (VDouble same) (VCars comm)
    =  newIORef V.empty >>= \result
    -> V.forM_ comm ( \(Car v n) ->
        case (same <= 1) of
            False -> return ()
            True  -> case isDetail情報産業 year (Car v n) of
                        False   -> modifyIORef' result (V.cons (Car v n))
                        True    -> modifyIORef' result (V.cons (Car (v * (1 - (same * 0.01) ) ) n))
                                >> modifyIORef' toMinusInfo ((v * (1 - (same * 0.01) ) ) + ))

    >> VCars <$> readIORef result >>= writeArray icr H事業所別生産物別売上高


f物品賃貸業削除 :: Year -> IOCensusRow ->  IORef Double ->  Val相手先別収入割合_サB -> Val事業所別生産物別売上高 ->  IO ()
f物品賃貸業削除 year icr toMinusRent Null           _             = return ()
f物品賃貸業削除 year icr toMinusRent _              Null          = return ()
f物品賃貸業削除 year icr toMinusRent (V相手先別収入割合 eRate) (VCars comm)
    =   let rate = _同一企業 eRate
    in  newIORef V.empty >>= \result
    ->  V.forM_ comm ( \(Car v n) ->
        case (rate <= 1) of
            False -> return ()
            True  -> case isDetail物品賃貸業 year (Car v n) of
                        False   -> modifyIORef' result (V.cons (Car v n))
                        True    -> modifyIORef' result (V.cons (Car (v * (1 - (rate * 0.01) ) ) n) )
                                >> modifyIORef' toMinusRent (+ (v * (1 - (rate * 0.01) ) ) ) )
    >> VCars <$> readIORef result  >>= writeArray icr H事業所別生産物別売上高

fその他のサB削除 :: Year -> IOCensusRow ->  IORef Double ->  Val相手先別収入割合_サB -> Val事業所別生産物別売上高 ->  IO ()
fその他のサB削除 year icr toMinusOth Null           _             = return ()
fその他のサB削除 year icr toMinusOth _              Null          = return ()
fその他のサB削除 year icr toMinusOth (V相手先別収入割合 eRate) (VCars comm)
    =  let rate = _同一企業 eRate
    in newIORef V.empty >>= \result
    ->  V.forM_ comm ( \(Car v n) ->
        case (rate <= 1) of
            False -> return ()
            True  -> case isDetailその他のサB year (Car v n) of
                        False   -> modifyIORef' result (V.cons (Car v n))
                        True    -> modifyIORef' result (V.cons (Car (v * (1 - (rate * 0.01) ) ) n) )
                                >> modifyIORef' toMinusOth (+ (v * (1 - (rate * 0.01) ) ) ) )
    >> VCars <$> readIORef result  >>= writeArray icr H事業所別生産物別売上高


-- | 22区分及び細分類でソフトウェア業，情報処理・提供サービス業か判定
{-# INLINE isDetail情報産業 #-}
isDetail情報産業 :: Year -> Car -> Bool
isDetail情報産業 24 ca | T.take 2 (name ca) == T.pack "39" = True
                       | T.take 2 (name ca) == T.pack "40" = True
                       | otherwise                         = False

isDetail情報産業 28 ca | T.take 2 (name ca) == T.pack "39" = True
                       | T.take 2 (name ca) == T.pack "40" = True
                       | otherwise                         = False


-- | 細分類で物品賃貸業か判定
{-# INLINE isDetail物品賃貸業 #-}
isDetail物品賃貸業 :: Year -> Car -> Bool
isDetail物品賃貸業 24 ca | T.take 2 (name ca) == T.pack "70" = True
                         | otherwise                         = False

isDetail物品賃貸業 28 ca | T.take 2 (name ca) == T.pack "70" = True
                         | otherwise                         = False



-- | 細分類で広告 ，警備業，プラントエンジニアリング業及び鉱物探査以外のその他の対事業所サービスかを判定
--
-- プラントエンジニアリング,鉱物探査の区別は不可なので,他に分類されないその他の対事業所サービス全体で適用
{-# INLINE isDetailその他のサB #-}
isDetailその他のサB :: Year -> Car -> Bool
isDetailその他のサB 24 ca | T.take 2 (name ca) == T.pack "73"   = True -- 広告
                          |          (name ca) == T.pack "9231" = True -- 警備業
                          |          (name ca) == T.pack "9299" = True -- 他に分類されないその他の対事業所サービス
                          | otherwise                           = False

isDetailその他のサB 28 ca | T.take 2 (name ca) == T.pack "73"    = True -- 広告
                          |          (name ca) == T.pack "9231"  = True -- 警備業
                          |          (name ca) == T.pack "9299"  = True -- 他に分類されないその他の対事業所サービス
                          | otherwise                            = False





-- ** 企業調査の取扱
------------------------------------------------------------------
{- |

    * ① 企業調査票産業の企業の傘下に事業所調査票産業を主業とする事業所が存在するケース

     このケースでは，企業調査票産業を主業とする企業の傘下事業所である，事業所調査票事業所の売上額等の情報は，
     事業所調査票で調査されており，且つその値は事業所調査票を元に集計が行われている．
     したがって，企業調査票の値全てを集計すると，事業所調査票で集計されている部分に関して重複が発生する．
     この重複を避けるために，企業調査票の集計単位を企業ではなく，
     事業所調査票で把握されている部分を除いた部分を一つの事業所とみなした仮想事業所として集計を行う．
     なお，このような処理が現行の推計において行われていることを示す資料を筆者は見つけることができなかったため，
     この試算は今後の課題としたい．


    * ② 事業所調査票産業の企業の傘下に企業調査票産業を主業とする事業所が存在する場合．
     事業所調査票産業を主業とする企業の，企業調査票の値は，通常集計には用いられないが，
     この企業の傘下事業所に企業調査票産業を主業とする事業所が存在した場合，その事業所の売上高等の値は，
     事業所調査票では調査されていない．したがって，この企業に関して事業所調査票のみを集計に用いた場合，
     その企業傘下の企業調査票産業を主業とする事業所の値が集計から欠損することとなる．
     これを避けるため，この企業傘下の事業所調査票産業を主業とする事業所の値を除いた部分を仮想事業所として集計に加える必要がある．
     この点に関して問題となるのは，特にサービス関連産業Bが企業調査票産業となることで，どの程度影響がでるかであるが，
     この点に関しても今後の試算による課題としたい．-}

f企業調査票処理 = undefined


-----------------------------------------------------------
-- * 副業の分解
-----------------------------------------------------------

-- | 県 1-47
type PrefInt = Int

-- | 22区分の事業 1 - 22
type BusiInt =  Int

-- | 産業細分類 1- 1617 余裕もたせて2000
type DetaInt = Int

-- | 県別22区分別産業細分類別のに対する比率のMap
type SubRateArray      = IOArray (PrefInt, BusiInt, DetaInt) Double

-- | からの副業比率
empSubRateArray :: IO SubRateArray
empSubRateArray = newArray ((1,0,0),(47,(VDC.numOf22分類-1),(VDC.numOf細分類-1))) 0

-- | 非副業困難部門
--
-- これでループを回すことで実質的に副業困難部門を抜いていることと同じにする.
--
--  今は副業困難部門なし(要修正)
{-# INLINE canBeSub #-}
canBeSub :: [Int]
canBeSub = [0 .. (VDC.numOf細分類 -1 )]

-- | 地域コードから県の番号に変換する関数
{-# INLINE area2Int #-}
area2Int :: Text -> PrefInt
area2Int tx = VCC.textToInt $ T.take 2 tx

-- | 事業分類からBusiIntに変換する関数
{-# INLINE busi2Int #-}
busi2Int ::  IndustryBusiness -> BusiInt
busi2Int tx = case Map.lookup tx VDC.ci22分類インデックス正順 of
                    Just deta -> fromIntegral deta
                    Nothing   -> error $ "error : busi2Int : Can not find deta " ++ T.unpack tx


-- | IntからBusinessに変換する関数
{-# INLINE int2Busi #-}
int2Busi :: BusiInt -> Industry
int2Busi num | num >= 1 && num <= 9   = T.pack $ "T0" ++ (ushow num)
             | num >= 10 && num <= 22 = T.pack $ "T"  ++ (ushow num)

-- | 細分類からDetaIot への変換
{-# INLINE deta2Int #-}
deta2Int ::  Industry -> DetaInt
deta2Int tx = case Map.lookup tx VDC.ci細分類インデックス正順 of
                    Just deta -> fromIntegral deta
                    Nothing   -> error $ "error : deta2Int : Can not find deta " ++ T.unpack tx

-- | DetaIot から への変換
{-# INLINE int2Deta #-}
int2Deta ::  DetaInt -> Industry
int2Deta num = case Map.lookup (toInteger num) VDC.ic細分類インデックス正順 of
                    Just deta -> deta
                    Nothing   -> error $ "error : int2Deta : Can not find deta " ++ ushow num


{- |
    これまでに行われた処理を経て，各事業所の22区分の事業別売上（収入）金額及び，
    主業に関する事業別商品別産出額が把握されたこととなる．

    しかし，22区分の主業以外の事業，即ち副業の内訳（主生産物及び副生産物）に関する詳細は把握されていない．
    実際の各事業所の副業の内訳は経済センサスの調査結果から把握されないため，
    ここでは，特定の事業所の副業に関して，その副業を主業とする事業所のデータを基に副業の値を按分することとする．
    副業の分解の手法に関しては，
    「平成23年（2011年）産業連関表 第13回 産業連関技術会議 配布資料（１）
    経済センサス-活動調査のデータを利用した国内生産額の推計について
    経済センサスから得られる副業データをIO部門に分解する方法案及び留意点 Ⅰ 基本的な計算方法」
    において，以下のように説明されている．

    組替集計から得られる主業ベースの部門別売上高Aを用いて部門別の比率Bを作る，
    この比率を，ひな形・統合分類ベースの総額しか分からない副業の売上高Cに乗じて，部門別の副業推計値Dを計算する．
    留意点

    ① 地域表作成の観点も踏まえ，可能な範囲で都道府県別に計算し，その積み上げをもって全国値とする．

    ② 副業として行えないことが明白な部門については，比率計算から除外する．

    同資料から引用 一部筆者編集

     この「副業として行えないことが明白な部門」に関しては，
     同資料中 「参考資料１ CT推計における経済センサスデータの利用予定（現時点での見込み．今後の変更有）」において，
     基本分類ごとにそれが，「他産業を主業とする事業所が，副業として行うことが困難」か否かが一覧表の形で掲載されており，
     獣医業，下水道，公共放送などが，副業困難部門として設定されている．
     ただし，当該資料は，表題の通り確定前の見込みであり，実際の設定は異なっているものと考えられる．
     実際，同会における議事概要では，

    > 例えば、「トラック・バス・その他の自動車」について、副業困難部門とされていないが、
    > 製造業以外の事業所で「トラック・バス・その他の自動車」の生産が可能ということか。
    > 特に製造業については、本日の資料で示されたもののほかにも、副業困難部門があると考えられる。
    >
    > →  産業格付については、一次統計においても難しい課題である。
    > 例えば、大規模に電気製品の生産・販売を行っている企業について、産業格付上、商業とされた場合、
    > 企業活動の基本になっている製造業の活動は副業なのかという問題もある。そういった意味で、主業・副業の区分は、
    > 様々な課題をはらんでいる。
    > →副業困難部門については、本日の御指摘を踏まえて、定義も含め、改めて整理させて頂く。
    >
    > 同資料，pp．3より引用

    といった議論が掲載されており，実際の推計時には大きく変更されていると考えられるが，
    筆者の探す限りではこの点に関する公表資料は存在しないものと思われる．
    基本的な推計手法は，先にみたように，県ごとに，副業別の総売上高に，
    事業所産業別・調査品目別売上高の比率を掛けることで，副業の分解がなされるが，
    同資料 「Ⅲその他の留意点」では，22区分の内，CT推計に経済センサスが用いられていない部門に関しては，
    副業データの分解作業は行わないとしている．本稿では，これらの部門に関しても，経済センサスの値を用いて，
    副業の分解を行うよう設計する．

    現段階では,副業困難部門の設定は行っていない(要修正)
-}

f副業の分解 ::  (MonadIO m)  => SubRateArray ->  ConduitT IOCensusRow IOCensusRow m ()
f副業の分解 sra =  await >>= \maybeIcr
                -> case maybeIcr of
                    Nothing  -> return ()
                    Just icr -> liftIO ( readArray icr H事業別売上高           >>= \valBusi
                                    ->   readArray icr H事業所別生産物別売上高 >>= \valComm
                                    ->   readArray icr H地域コード             >>= \valArea
                                    ->   readArray icr H産業格付               >>= \valKind
                                    ->   f副業の分解処理 sra icr valArea valBusi valComm valKind)
                             >> yield icr
                             >> f副業の分解 sra
{- |
地域コードがない場合,新潟(15)の割合を使う(地域コードがないことはほぼないはず)

事業別売上高がない場合は何もしない
 -}

f副業の分解処理 :: SubRateArray -> IOCensusRow -> Val地域コード -> Val事業別売上高 -> Val事業所別生産物別売上高 -> Val産業格付 -> IO ()
f副業の分解処理 sra icr valArea      Null         valComm  valKind = return ()
f副業の分解処理 sra icr (VText area) (VCars busi) valComm  valKind
    =  let prefInt = area2Int area
    in newIORef [] >>= \ refToAdd
    -> V.forM_ (deleteMain valKind valComm busi) ( \(Car va na)
        -> let busiInt = busi2Int na
        in CMP.forM_ canBeSub ( \detaInt
            -> readArray sra (prefInt, busiInt, detaInt) >>= \rate
            -> let newName = int2Deta detaInt
            in when (rate /= 0.0) (modifyIORef' refToAdd ((Car (rate * va) newName):))))
    >> readIORef refToAdd >>= \toAdd
    -> case valComm of
        Null        -> writeArray icr H事業所別生産物別売上高 $ VCars $ V.fromList toAdd
        VCars comm  -> writeArray icr H事業所別生産物別売上高 $ VCars $ (V.++) comm  $ V.fromList toAdd

f副業の分解処理 sra icr Null         (VCars busi) valComm  valKind = f副業の分解処理 sra icr (VText (T.pack "15")) (VCars busi) valComm  valKind -- 新潟


-- | 主業分も分解しないように主業を事業別売上高から削除する
--
--   事業所別生産物別売上高がない場合は主業分も入れる
deleteMain :: Val産業格付 -> Val事業所別生産物別売上高 -> Cars事業別売上高 -> Cars事業別売上高
deleteMain _                 Null        busi =  busi
deleteMain (V産業格付 kind) (VCars comm) busi | V.null comm = busi
                                              | otherwise   = case (elevateStratum (_15分類 kind) Business) of
                                                                Just tt -> V.filter (\x -> name x /= tt ) busi
                                                                Nothing -> busi
deleteMain Null             (VCars comm) busi = busi





f副業比率作成 ::  (MonadIO m)  => SubRateArray ->  ConduitT IOCensusRow Void m SubRateArray
f副業比率作成 sra
    =  await >>= \maybeIcr
    -> case maybeIcr of
        Nothing   -> liftIO (culcSRA sra) >>= return

        Just icr  -> liftIO (  readArray icr H産業格付               >>= \ !valKind
                            -> readArray icr H地域コード             >>= \ !valArea
                            -> readArray icr H事業所別生産物別売上高 >>= \ !valComm
                            -> f副業比率作成処理 sra valKind valArea valComm )
                  >> f副業比率作成 sra

    where
    -- 総額になっているところを比率に治す
    culcSRA :: SubRateArray -> IO SubRateArray
    culcSRA sra = return sra
                <* do
                CMP.forM_ [1 .. 47] $ \pref -> do
                    forM_ [0 .. (VDC.numOf22分類-1)] $ \ !busi -> do
                        refTotal <- newIORef 0
                        forM_ canBeSub $ \ !deta -> do
                                tmoVal <-  readArray sra (pref, busi, deta)
                                total  <-  readIORef refTotal
                                modifyIORef' refTotal (total +)

                        total <- readIORef refTotal
                        forM_ canBeSub $ \ !deta -> do
                                tmpVal <- readArray  sra (pref, busi, deta)
                                if total /= 0   then writeArray sra (pref, busi, deta) (tmpVal / total)
                                                else writeArray sra (pref, busi, deta) 0




f副業比率作成処理   :: SubRateArray
                    -> Val産業格付
                    -> Val地域コード
                    -> Val事業所別生産物別売上高
                    -> IO ()
f副業比率作成処理 sra Null              valArea      valComm      = return ()
f副業比率作成処理 sra valKind           Null         valComm      = return ()
f副業比率作成処理 sra valKind           valArea      Null         = return ()
f副業比率作成処理 sra (V産業格付 eKind) (VText area) (VCars comm)
    =  let (Just ~busiTx)  = VDC.elevateStratum (_15分類 eKind) VDC.Business -- 元の産業格付けを使ってる場合15,35でエラーになる
    in let busiInt    = busi2Int busiTx
    in let prefInt    = area2Int area
    in let notSub     = V.filter (\x -> (name x) `VDC.isMemberOf` busiTx) comm
    in V.forM_ notSub $ \ca
        -> let detaInt = deta2Int (name ca)
        in readArray  sra (prefInt, busiInt, detaInt) >>= \ !curVal
        -> writeArray sra (prefInt, busiInt, detaInt)
        $  curVal + (value ca)

{- |
    本稿の主題の一つが，現行のセンサスの値を用いて，どの程度細かい部門のV表が推計できるかという点に関するものであるが，
    同資料において，「細品目の構成についてCTの構成過程で変動する可能性があること」，
    「副業が困難か否かについて，基本分類ごとにしか判断していないこと」から，
    「副業データの分解は，基本分類の単位で行う」ものとしている．従って，現行のセンサスの組替集計の範囲では，
    基本分類がV表（S表）を構成可能な最小の部門分類であるといえる．しかし，この２点に関しては，事前にそれぞれを定義することで，
    解決できることから，原理的にはより細かい部門での推計が可能であることも示唆されている．

    県別に集計することに関して，同資料 「Ⅱ 比較データの作成」では，
    「県ごとに計算した結果を積み上げて全国値にすることとしているが，県ごとの特徴が，
    どの程度影響を及ぼしているかについて，現時点で検証することはできない」とある．

    この現時点というのは，平成28年経済センサス集計前という意味であろうから現在においては，
    既に県別の特徴が検証されているものと思われるが，その結果に関する資料は見つけることができなかった．
    いずれにせよ，このように集計単位をある程度の同質性を仮定して小さくすることは集計上有用であると思われ，
    地域ごとに産業は異なる特徴を持つというのは案に産業技術仮定を否定していることとなる．その観点からすると，
    一点現行の推計方法には不合理な点が見受けられる．それは，V表の推計に当たって組替集計を経由して，
    一度集計されたものを編纂するという形をとっている点である．現在では，経済センサスの個票レベルの情報を
    一度事業所産業別事業別売上額及び，事業所産業別調査品目売上額の形で集計し，その比率を用いてV表を作成している．
    これはいうなれば同一の産業に属する商品は同一の技術構造を持つという商品技術仮定を用いていることを意味するが，
    先の地域区分によって産業技術仮定を否定したのと同様に，商品技術仮定を置かないような推計手法を取り入れる態度の方が
    一貫性があるといえる．現在このような形をとっているのは，経済センサスの集計を独立行政法人 統計センターが請け負い，
    組替集計を用いてV表の推計を総務省が行うという体制によるものであると考えられるが，経済センサスから一貫して，
    V表を推計し，事業所毎の特性によって一定の区分をつけた上で，副業の分解等を行うことで，
    商品技術仮定を置かないV表の推計が可能であると思われる．本稿では，その実際の試算を行わないが，
    今後の研究課題として，残しておきたい．-}

f副業把握改善版 = undefined



-----------------------------------------------------------
-- * CT推計
-----------------------------------------------------------
{- |
    現行のV表の作成においては，V表の列和，
    即ち商品別総産出額（Control Total）を主に経済センサスを含む各種基礎調査から
    推計された取引基本表の行部門をV表列部門に組み替えた値を固定値として用いており，
    センサスから得られた各種データを利用してCTを各産業に案分する処理を行っている．

    本稿では，可能な限り経済センサスデータからCTを直接取得することを試みるが，
    実際のV表の算出におけるCTに経済センサスの値が用いられている部門は限定的である．
    第13回産業連関技術会議資料 によれば平成23年産業連関表取引基本表では，平成17年以前において工業統計，
    商業統計又はサービス業基本統計をCT推計において利用していた製造業，商業，サービス業などの分野に関しては，
    経済センサスデータを基礎資料として利用している．一方それ以外の分野のうち農林漁業は，
    個人経営の農林漁家が経済センサスの調査対象となっていないため，その他の分野に関しては「経済センサス以外の情報で推計する方が，
    より正確かつ効率的である」ため用いていないとしている

    以降，平成23年産業連関表においてCT推計にセンサスを用いた部門の推計手法及びその問題点に関して論じたのち，
    用いていない部門に関して経済センサスからCTを推計した場合どのようなものになるか検討する．


    _5.2.1   経済センサスをCT推計に用いている部門_

    サービス部門

    平成23年IOでは，サービス部門のCT推計に経済センサスの値を用いているが，
    経済センサスにおけるサービス部門には未把握部分が大きいという問題がある．
    第13回産業連関技術会議資料 によればサービス業の売上等未把握率は「情報通信業の内，40 インターネット付随サービス業」
    において33.3%，「宿泊業，飲食サービス業」において26%，「
    サービス業（他に分類されないもの）」において20%に上り，
    「製造業」の12.80％，「農業，林業」の16.30%，「卸売業，小売業」における17．50%などサービス業と比較すれば高い値であるといえる．

    第13回産業連関技術会議資料 では，サービス部門のCT推計において，まず事業所を，
    主業，副業ごとに「売上高及び重要者数ともに把握された事業所（売上把握分）」
    「従業者数は把握されたが，売上高が把握されなかった事業所（売上未把握分）」の２区分で分割し，
    そのうち，主業に関して把握分・未把握分双方の売り上げを以下のように推計している．

    産業連関表の部門分類をCIO,部門分類の内サービス産業に該当する部分をCIOS⊂ CIO,経済センサスの産業分類をCCとして，
    ある部門 \(ω \in CIOS \)と対応付けられる \(ω' \in ' CC \)とすると，
    ω の主業相当の把握及び未把握部分の生産額 \( CT_main [ω] \) は，以下の式で求められる．

    \[ CT_{main}=SPP[ω] \times compInvEmp[ω'] \times activityRate[ω] \]

    where

    \[ SPP[ω]= \frac{sales[ω]}{invEmp[ω]} \]

    \[ activityRate[ω']= \frac{invEmp[ω]}{compTotalEmp[ω'] \times \frac{compInvEmp[ω']}{totalEmp[ω']}} \]

    なお，各変数は以下に従う．

    * _SPP[ω]（Sales per person）_

    ：ω∈CIOS 産業の一人あたり売上高

    * _sales[ω]_

    : ω∈CIOS の売上高．IOの部門分類に，経済センサス調査結果を組み替えた組替集計（非公表）より取得．

    * _invEmp[ω](Number of involved employment)_

    : 産業ω∈CIOSの従業者数のうち，派遣，出向等で外部に送り出している従業員を除いた従業員数（事業従業員数）．(\ ω \in CIOS \)に関しては組替集計より取得．

    * activetyRate[ω']

    :アクティビティ率; 事業所の従業者の内，その事業所の産業格付け \( ω’\in CC \)に従事している人数の割合

    * compInvEmp[ω‘] (Complete Number of involved employments)

    :ω ∈ CIOSと対応付けられた\( ω' \in CC )に産業格付けされ売上未把握分を含めた事業所の事業従業員数．経済センサス第４ 表より取得．

    * _totalEmp[ω](Total number of employments)_

    :産業 \( ω’\in CC \) の総従業者数．経済センサス第２-1-1表 より取得．

    * _compTotalEmp[ω’] (Complete Total Number of Employments)_

    : \( ω \in CIOS \)と対応付けられたω∈CCに産業格付けされた売上未把握分を含めない事業所の従業員数．経済センサス第４表または経済センサス第２表 より取得(第２表は産業細分類まで把握可能)

    この時 CT_{main}を変形すると，項が打ち消しあい，

    \[ CT_{main}[ω] = sales[ω] * \frac{totalEmp[ω']}{compTotalEmp[ω']} \]

    が得られる．

    製造部門・商業部門
    製造部門及び，商業部門におけるCT推計では，

    > ①  従前からも，全数調査（工業統計調査，商業統計調査）のデータを使用して，把握された範囲で推計していること
    > ② 今回の経済センサスにおいても未把握分が比較的小さいこと
    > ③生産動態統計調査など，比較可能なデータがあること
    > 産業連関技術会議資料 より抜粋（一部筆者編集）

    の3点から，サービス業で行われている従業者数による補完を行わず，
    生産動態統計調査，商業統計調査などのデータによる調整のもと売上高が把握された事業所の範囲で推計を行う方針であると説明されている．従って，平成23年産業連関表のCTには、「製造業」における12.80%，「卸売業，小売業」における17.50%の売上高未把握分は基本的には含まれていない．
    野村.他（2017）では，商業部門におけるこの未把握分の影響として平成23年産業連関表における商業マージン額の過小評価額が
    凡そ7.1-12.3兆円に上ると試算しており，未把握分の補定作業を重要な検討課題として掲げている．
    なお，同論文においては，未把握分事業所の従業者数を最大ケースで99人以下，最小ケースで29人以下として，
    業種別・従業者規模別の１事業所あたり商品販売額を乗ずることによって未把握分マージン額の試算を行っている．

    前述のサービス業においては，そのCT_mainは経済センサスにおける売上高の和であるが，製造部門及び，商業部門におけるCTの計算はいくつかの点でサービス業とは異なる．
    まず，製造業及び，商業において産出額を推計するには，在庫の算出も含めて試算する必要がある．この点に関しては，前述の在庫品評価調整の節にて論じている．
    次にSNAにおいて商業における算出額は，商品の販売額ではなく，商業マージンを対象としており，「商業マージン=商品販売額-商品仕入れ額」として定義される．この点に関しては， 「4.6章 マージン推計」において詳しく扱っている．

    経済センサスをCT推計に用いていない部門
    製造業，サービス業，商業以外の部門に関しては，経済センサスをCT推計に用いていないためその推計手法が公には存在していない．その為，本稿では，サービス業と同様の従業員数による売り上げの補定を行ったうえで，その売上の総和をCTとして扱う．
    調査対象外産業の扱い
    以下の部門に関しては，センサスで売り上げを得ることができない．

    > ・農業，林業，漁業の個人経営事業所の売り上げ
    > ・家事サービス業の事業所の売り上げ
    > ・国及び地方公共団体の売り上げ
    > ・自家発電などの自家生産・自己消費

    これらの部門に関しては，本稿では取り扱わず，それぞれの部門の自交点には０が計上される．

    fCT推計では,これらの乗数を求める

    また,使用しない企業のデータや,団体のデータ,ネットワーク産業の事業所のデータを抜かす
-}

fCT乗数推計 :: (MonadIO m) => IORef ToMakeCTMultiplier ->  ConduitT IOCensusRow Void m CTMultiplier
fCT乗数推計 refTmcm
    =  await >>= \maybeIcr
    -> case maybeIcr of
        Nothing  -> liftIO (readIORef refTmcm) >>= return.makeCTMultiplier
        Just icr -> liftIO (readArray icr H総売上)       >>= \ !valSales
                 -> liftIO (readArray icr H雇用情報)     >>= \ !valEmp
                 -> liftIO (readArray icr H産業格付)     >>= \ !valClas
                 -> liftIO (readArray icr H調査票の種類) >>= \ !valKind
                 -> liftIO (fCT乗数推計処理 refTmcm valSales valEmp valClas valKind)
                 >> fCT乗数推計 refTmcm


fCT乗数推計処理 :: IORef ToMakeCTMultiplier -> Val総売上 -> Val雇用情報 -> Val産業格付 -> Val調査票の種類 -> IO ()
fCT乗数推計処理 refTmcm valSales (V雇用情報 emp) (V産業格付 clas) (V調査票の種類 kind)
    = case correctPair kind of
        Wrong -> return ()
        ES    -> f _事雇用者数 refTmcm emp clas
        EN    -> f _企雇用者数 refTmcm emp clas
    where
    f :: (E雇用情報 -> Int) -> IORef ToMakeCTMultiplier -> E雇用情報 -> E産業格付 -> IO ()
    f g refTmcm emp clas
        =  let smallInt  = small2Int (_小分類 clas)
        in let totalEmp  = fromIntegral (g emp)
        in readIORef refTmcm >>= \tmcm
        -> case valSales of
            Null   -- 売上未把握分
             -> case Map.lookup smallInt tmcm of
                    Nothing                   -> modifyIORef' refTmcm (Map.insert smallInt (totalEmp, 0))
                    Just (cTotalEmp,cCompEmp) -> modifyIORef' refTmcm (Map.insert smallInt (cTotalEmp + totalEmp, cCompEmp))

            (VDouble sales) -- 売上把握分
             ->  case Map.lookup smallInt tmcm of
                    Nothing                   -> modifyIORef' refTmcm (Map.insert smallInt (totalEmp, totalEmp))
                    Just (cTotalEmp,cCompEmp) -> modifyIORef' refTmcm (Map.insert smallInt (cTotalEmp + totalEmp, cCompEmp + totalEmp))



fCT乗数推計処理 icr _ _ _ _  = return ()

-- | EN か ES か Wrongか
data ENESPair = EN | ES | Wrong deriving (Eq, Show)

-- | ネットワーク産業かつ企業調査票または非ネットワークかつ事業所調査票の判定
{-# INLINE correctPair #-}
correctPair :: E調査票の種類 -> ENESPair
correctPair kind |     isNetwork kind  &&      isEN kind   = EN
                 | not(isNetwork kind) && not (isEN kind)  = ES
                 | otherwise                               = Wrong

    where
    --  | ネットワーク産業か判定する
    isNetwork :: E調査票の種類 -> Bool
    isNetwork kind  | _対象産業 kind == E建設サービスA     = True
                    | _対象産業 kind == E建設サービスA学校 = True
                    | _対象産業 kind == E団体              = True
                    | otherwise                            = False
    --  | 企業調査票かの判定
    isEN (E調査票の種類 kind target subject)
        | kind    == E企業調査票     = True
        | kind    == E団体調査票     = True
        | subject == E団体法人用     = True
        | otherwise                  = False



-- | 産業小分類 0 - 603
type SmallInt = Int

-- | 中分類からMidIit への変換
{-# INLINE small2Int #-}
small2Int ::  Industry -> SmallInt
small2Int tx = case Map.lookup tx VDC.ci小分類インデックス正順 of
                    Just deta -> fromIntegral deta
                    Nothing   -> error $ "error : mid2Small : Can not find in small " ++ ushow tx

-- | SmallInt から中分類への変換
{-# INLINE int2Small #-}
int2Small ::  SmallInt -> Industry
int2Small num = case Map.lookup (toInteger num) VDC.ic小分類インデックス正順 of
                    Just deta -> deta
                    Nothing   -> error $ "error : int2Small : Can not find in small " ++ ushow num


-- | 産業別に乗じる補定の乗数
type CTMultiplier = Map SmallInt Double

-- | 売上未把握分を含めない産業の従業者数
type CompTotalEmp = Double

-- | 売上未把握分を含めた産業の従業者数
type TotalEmp     = Double

type ToMakeCTMultiplier = Map SmallInt (TotalEmp, CompTotalEmp)

makeCTMultiplier :: ToMakeCTMultiplier -> CTMultiplier
makeCTMultiplier tmcm = Map.map f tmcm
  where
  f :: (TotalEmp, CompTotalEmp) -> Double
  f (t, c)  | c == 0    = 1
            | (t/c) < 1 = 1
            | otherwise = (t/c)




-----------------------------------------------------------
-- * 産業別生産物別別産出額の把握
-----------------------------------------------------------
type IndustryInt  = Int
type CommodityInt = Int

-- | 産業別生産物別の産出額を記録したArray
--
-- 行が産業， 列が生産物
type IndCommArray = IOArray (IndustryInt, CommodityInt) Double

empICASmallDetail :: IO IndCommArray
empICASmallDetail  = newArray ((0,0), (VDC.numOf小分類 - 1, VDC.numOf細分類 - 1)) 0

-- | Tableをそのまま出力する
writeVTable :: FilePath -> IndCommArray ->  IO ()
writeVTable outputFile ica
    =   getBounds ica >>= \ (start, end)
    ->  let maxSmallInt = fst end
    in  let maxDetaInt  = snd end
    in  withFile outputFile WriteMode $ \ wHandle
    ->  forM_ [0 .. maxSmallInt] $ \ !smallInt
    ->  forM [0 .. maxDetaInt] ( \ !detaInt
    ->  T.pack.show <$> (readArray ica (smallInt,detaInt) :: IO Double))
    >>= CSV.hPutCsvLn wHandle


type IndustrySize = Int

readTable :: FilePath -> (IndustrySize, IndustrySize) -> IO IndCommArray
readTable inputFile (i,c) =  empICASmallDetail  >>= \ica
                          -> withFile inputFile ReadMode ( \ rHandle
                            -> forM_ [0 .. (i - 1)] ( \ !smallInt
                                -> (L.head <$> parseCSVErr <$> TO.hGetLine rHandle) >>= \ !line
                                -> forM_ [0 .. (c - 1)] ( \ !detaInt
                                    -> writeArray ica (smallInt, detaInt) (VCC.textToDouble (line !! detaInt)))))
                        >> return ica



{- |
V表の作成に利用される経済センサス組替集計は，
「事業所産業別調査品目別売上額」及び，「事業所産業別・事業別売上額」である．

本章で定義してきた諸々の処理を組み合わせることで，
センサス分類における事業所別商品別産出額及び産業別商品別産出額を求めることが可能となる．
基本的には，価格変換，在庫品評価調整，事業所別生産物別生産量把握，企業の事業所への分割，
マージン推計の順に処理を行い，副業の分解をすることで，事業所別商品産出額が求められ，
事業所別商品産出額を産業別に集計することで，産業別商品別産出額が求められる．
-}

f産業別生産物別産出額 ::  (MonadIO m) => CTMultiplier -> IndCommArray -> ConduitT IOCensusRow Void m IndCommArray
f産業別生産物別産出額 ctm ica
    =  await >>= \maybeIcr
    -> case maybeIcr of
        Nothing   -> liftIO (multipleICA ctm ica) >> return ica
        Just icr  -> liftIO (readArray icr H事業所別生産物別売上高) >>= \ valComm
                  -> liftIO (readArray icr H産業格付 )              >>= \ valClas
                  -> liftIO (readArray icr H調査票の種類)           >>= \ valKind
                  -> case valKind of
                      Null               -> f産業別生産物別産出額 ctm ica
                      V調査票の種類 kind -> case correctPair kind of -- 企業調査票等の値を抜く
                                              EN    -> liftIO (f産業別生産物別産出額処理 ica valComm valClas)
                                                    >> f産業別生産物別産出額 ctm ica
                                              ES    -> liftIO (f産業別生産物別産出額処理 ica valComm valClas)
                                                    >> f産業別生産物別産出額 ctm ica
                                              Wrong -> f産業別生産物別産出額 ctm ica
    where
    multipleICA :: CTMultiplier -> IndCommArray -> IO ()
    multipleICA ctm ica =  let ctmList =  Map.toList ctm
                        in CMP.forM_ ctmList     $ \ (!smallInt, !multi)
                        -> CMP.forM_ [0 .. (VDC.numOf細分類 - 1)] $ \ !detaInt
                        -> readArray  ica (smallInt, detaInt) >>= \ !cv
                        -> writeArray ica (smallInt, detaInt) (cv * multi)

{-# INLINE f産業別生産物別産出額処理 #-}
f産業別生産物別産出額処理 :: IndCommArray -> Val事業所別生産物別売上高 -> Val産業格付 -> IO ()
f産業別生産物別産出額処理 ica Null         _                =  return ()
f産業別生産物別産出額処理 ica (VCars comm) valClass
    = case valClass of
        Null           -> let !smallInt = small2Int "△△△"       in f ica smallInt comm
        V産業格付 clas -> let !smallInt = small2Int (_小分類 clas) in f ica smallInt comm
        where
        f :: IndCommArray ->  SmallInt -> Cars -> IO ()
        f ica smallInt comm =  V.forM_ comm $ \(Car va na)
                            -> let !detaInt = deta2Int na
                            in readArray  ica (smallInt, detaInt) >>= \ !cv
                            -> writeArray ica (smallInt, detaInt) (cv + va)




------------------------------------------------------------------
-- * 部門名の変換 (センサス分類からIO分類への変換)
------------------------------------------------------------------

{- |
産業格付けNullの場合 格付け不明へ振替

部門内格付け不明及び,管理補助的業務は,全て近隣部門に比例按分する(どのように処理しているのか不明.)

くず・廃物
7466 00 製造工程からでたくず・廃物

に関して 製造業の段階で発生部門に振り分け



また，屑・副産物に関しては，取引基本表における屑・副産物発生部門をV表産業分類へ組替え，その値をセンサスから求められた産業×商品表の当該交点に計上している．

 本稿ではV表の作成は大まかに，以下①~⑤の作業を想定している．
なお，現行のV表の作成においては，屑，副産物の推計において取引基本表を経由しており，経済センサス以外の各種基礎統計値もその推計に利用している．
 本研究は，飽くまで同一データを利用することで推計手法毎の差異を分析することを目的としており，センサスデータから直接的に値を構成するという点で，
推計手法が現行のものとは異なる．
幾つかの補足できない概念等もそのまま未把握として扱い，大きな項目については他の統計を用いて簡易的に推計するなど，簡易的作成手法を採用する．

-}



-- | 細分類 -> 小分類への振替
f細分類振替 :: IOArray (SmallInt, DetaInt) Double  ->  IO (IOArray (SmallInt, SmallInt) Double)
f細分類振替 sd  =   ((newArray ((0,0),((VDC.numOf小分類 - 1), (VDC.numOf小分類 - 1))) 0.0) :: IO (IOArray (SmallInt, SmallInt) Double)) >>= \ initial
                ->  forM_ [0 .. (VDC.numOf小分類 - 1)]  (\smallInt ->
                        forM_ [0 .. (VDC.numOf細分類 - 1)] ( \detaInt ->
                            case elevateStratum (int2Deta detaInt) Small of
                                Nothing            -> putStrLn ("f細分類振替:" ++ show (int2Deta detaInt)) >> return ()
                                Just newSmall      -> let newSmallInt = small2Int newSmall
                                                   in readArray  sd      (smallInt, detaInt)     >>= \ tempDetaVal
                                                   -> readArray  initial (smallInt, newSmallInt) >>= \ tempSmallVal
                                                   -> writeArray initial (smallInt, newSmallInt) (tempDetaVal + tempSmallVal)))
                >>  return initial




{- |  f管理補助的業務振替, f格付け不能振替に使用

比例按分するが, 配分先の値が0の場合は等分する

振替先が全て0だった場合等分すると,ほぼ全てのセルに値が入ってしまう.

振替先が全て0だった場合には,その商品/産業按分先のの自交点に飛ばす.

経済センサスにおける分類では, V表の分類における｢111 分類不明｣のように分類全体に
おける格付け不能の他に, ｢農林水産業内格付け不能｣, ｢耕種農業内格付け不能｣のように幾つかの段階別に格付け不能が存在する.
これらの格付け不能の段階が,V表の分類よりも細かい場合には,対応するV表の分類にその値を計上することが可能であるが,
｢農林水産業内格付け不能｣などは, V表の部門に振り分ける以前に, 経済センサスにおける他の部門に事前に振り分ける必要性がある
   本稿では, それらの格付け不能の商品及び産業に対して,｢格付け不能の振替先と想定される候補｣(｢農林水産業内格付け不能｣に対して,
   ｢耕種農業｣,｢畜産｣,｢農業サービス｣,｢林業｣,｢漁業｣など)を選定し,それらの部門に計上されている値に比例して按分している.
しかし, ｢格付け不能の振替先と想定される候補｣の振り分け前の値が全て0であった場合は,
それらのセルに按分はせず,その振り分け先の産業,商品の自交点に等分して計上している.
この処理によって,幾つかの部門の自交点の値が実際の値よりも過剰になることが予想される点に留意されたい.
 自交点に振り分ける際にも,本来であれば等分を行うよりも,比例按分を行う方がより正確なものとなることが予想されるが,
 自交点の値が0であった場合に別の値を参照する必要があり,その参照値が0で会った場合にと切りがなくなるため,このような処理となった.


-}

f近隣部門振替   :: IOArray (SmallInt, SmallInt) Double
                -> Map Industry [Industry]
                -> IO ()
f近隣部門振替 xs ms = do
    let ks = Map.keys ms
    forM_ ks $ \ k -> do -- 管理補助的業務の小分類
        forM_ [0 .. (VDC.numOf小分類 - 1)] $ \smallInt -> do -- 行を分配
                tempSum     <- newIORef 0.0
                tempDistVal <- readArray xs (smallInt, small2Int k) -- 分配されるある産業(smallInt)の管理補助的業務(k)
                case (tempDistVal == 0) of
                    True  -> return()
                    False -> do
                        writeArray xs (smallInt, small2Int k) 0 -- 管理補助的業務の小分類分配されるので０置き
                        let maybeVs = Map.lookup k ms
                        case maybeVs of
                            Nothing -> print ("近隣部門振替:" ++ show(k) ++ "該当する部門がありません.") >> return ()
                            Just vs -> do
                                forM_ vs ( \ v -> do
                                    temp <- readArray xs (smallInt, small2Int v) -- 産業smallIntの分配先 v
                                    case (temp == 0) of
                                        True  -> return ()
                                        False -> modifyIORef' tempSum (temp +))

                                forDiv  <- readIORef tempSum
                                case (forDiv == 0) of
                                    True  -> let num = fromIntegral (L.length vs)
                                          in forM_ vs ( \ v -> readArray  xs (small2Int v, small2Int v) >>= \temp
                                                            -> writeArray xs (small2Int v, small2Int v) (temp + (tempDistVal / num)))

                                    False -> forM_ vs ( \ v -> do
                                        temp <- readArray xs (smallInt, small2Int v)
                                        case (temp == 0) of
                                            True  -> return ()
                                            False -> writeArray xs (smallInt, small2Int v) (temp + (tempDistVal * (temp / forDiv))))

        forM_ [0 .. (VDC.numOf小分類 - 1)] $ \smallInt -> do -- 行を分配
                tempSum     <- newIORef 0.0
                tempDistVal <- readArray xs (small2Int k, smallInt) -- 分配されるある産業(smallInt)の管理補助的業務(k)
                case (tempDistVal == 0) of
                    True  -> return()
                    False -> do
                        writeArray xs (small2Int k, smallInt) 0 -- 管理補助的業務の小分類分配されるので０置き
                        let maybeVs = Map.lookup k ms
                        case maybeVs of
                            Nothing -> print ("近隣部門振替:" ++ show(k) ++ "該当する部門がありません.") >> return ()
                            Just vs -> do
                                forM_ vs ( \ v -> do
                                    temp <- readArray xs (small2Int v, smallInt) -- 産業smallIntの分配先 v
                                    case (temp == 0) of
                                        True  -> return ()
                                        False -> modifyIORef' tempSum (temp +))

                                forDiv  <- readIORef tempSum
                                case (forDiv == 0) of
                                    True  -> let num = fromIntegral (L.length vs)
                                          in forM_ vs ( \ v -> readArray  xs (small2Int v, small2Int v) >>= \temp
                                                            -> writeArray xs (small2Int v, small2Int v) (temp + (tempDistVal / num)))

                                    False -> forM_ vs ( \ v -> do
                                        temp <- readArray xs (small2Int v, smallInt)
                                        case (temp == 0) of
                                            True  -> return ()
                                            False -> writeArray xs (small2Int v, smallInt) (temp + (tempDistVal * (temp / forDiv))))




-- | 管理補助的業務の振替
--
-- 管理補助的業務を近隣部門に比例按分する.

f管理補助的業務振替 :: IOArray (SmallInt, SmallInt) Double -> IO (IOArray (SmallInt, SmallInt) Double)
f管理補助的業務振替 xs = f近隣部門振替 xs ss管理補助的業務 >> return xs


-- | 格付け不能の振替
f格付け不能振替 :: IOArray (SmallInt, SmallInt) Double -> IO (IOArray (SmallInt, SmallInt) Double)
f格付け不能振替 xs = f近隣部門振替 xs ss格付け不能 >> return xs




type VArray = IOArray (Int, Int) Double


-- | V表分類 0 - 124
type VInt = Int

-- | V表分類からVIntへの変換
{-# INLINE v2Int #-}
v2Int ::  IndustryV -> VInt
v2Int tx = case Map.lookup tx VDC.ciV表分類インデックス正順 of
                    Just deta -> fromIntegral deta
                    Nothing   -> error $ "error : v2Int : Can not find" ++ ushow tx

-- | VInt からV表分類への変換
{-# INLINE int2v #-}
int2v ::  VInt -> IndustryV
int2v num = case Map.lookup (toInteger num) VDC.icV表分類インデックス正順 of
                    Just deta -> deta
                    Nothing   -> error $ "error : int2V : Can not find " ++ show num

{- | センサス分類からIO分類への変換

    格付け不能と管理補助的業務の列,行はここで消える.

    V表分類の方が細かい項目,分類の合わない項目に関しては,(暫定的に)等分

-}

fV表変換 :: IOArray (SmallInt, SmallInt) Double -> IO (IOArray (VInt, VInt) Double)
fV表変換 sd =  ((newArray ((0,0),(VDC.numOfV表分類 - 1, VDC.numOfV表分類 - 1)) 0.0) :: IO (IOArray (VInt, VInt) Double)) >>= \ !initial
            -> forM_ [0 .. (VDC.numOf小分類 - 1)] ( \smallIntFst
                -> case (Map.lookup (int2Small smallIntFst) cc小分類V表分類) of
                    Nothing    ->  putStrLn ("fv表返還" ++ ushow (int2Small smallIntFst)) >> return ()
                    Just vintFsts -> let divNumFst = fromIntegral (length vintFsts)                                             -- 等分するための分母1つめ
                                  in forM_ (L.map v2Int vintFsts) ( \vintFst
                                        -> forM_ [0 .. (VDC.numOf小分類 - 1)] ( \smallIntSnd
                                            -> readArray sd (smallIntFst, smallIntSnd) >>= \ toAdd
                                            -> case (Map.lookup (int2Small smallIntSnd) cc小分類V表分類) of
                                                    Nothing         -> putStrLn ("fv表変換" ++ ushow (int2Small smallIntSnd)) >> return ()
                                                    Just vintSnds   -> let divNumSnd = fromIntegral (length vintSnds)           -- 等分するための分母2つめ
                                                                    in forM_ ( map v2Int vintSnds) ( \vintSnd
                                                                        -> readArray  initial (vintFst, vintSnd) >>= \ currentDob
                                                                        -> writeArray initial (vintFst, vintSnd) ((toAdd / (divNumFst * divNumSnd)) + currentDob) ))))
            >> return initial
------------------------------------------------------------------
------------------------------------------------------------------








