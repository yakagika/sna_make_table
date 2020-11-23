
{-# LANGUAGE  TemplateHaskell,  BangPatterns, UnboxedTuples, DeriveGeneric, StrictData, Strict#-}

{- |
        Module     : VTable.Data.Structure
        Copyright  : (c) Kaya Akagi. 2018-2019
        Maintainer : akagi15@cs.dis.titech.ac.jp


        * V表作表のためのデータ型や基本的なデータ型や,処理用の関数をまとめたモジュール
        * 表記を統一するために日本語を使っているので、等幅フォント推奨


        * エンコーディングに関して

            > 入出力も含めてすべてUTF-8で統一する
            > Windowsでの起動は想定していないの，Dockerを利用して，Linux上で動かすこと
            > Docker for Windows を利用する場合はchcp 65001をしないとTemplateHaskell部分のコンパイルが通らない．
            > Docker tool box はUTF-8 対応で死ぬので使わない．

        * Read に関して

            > すべてRead型のInstans となっているが，read関数は遅すぎるのでparserで読むこと．


        * コメントに関して

            > Haddock 前提
--          > Error でタグ付けして，問題点指摘
-}

module VTable.Data.Structure where

import qualified    Data.Vector                     as V
import qualified    Data.Vector.Mutable             as MV
import qualified    Data.Map.Strict                 as Map
import              Data.Map.Strict                 (Map)
import qualified    Data.Text                       as T
import              Data.Text                       (Text)
import qualified    Data.Text.Encoding              as E
import qualified    Data.Text.IO                    as TO
import qualified    Data.List                       as L
import qualified    Data.Maybe                      as Maybe
import              Data.ByteString                 (ByteString)
import qualified    Numeric                         as N
import              Data.Vector                     (Vector)
import              Data.Array.IArray
import              Data.Array.ST
import              Data.Array.IO
import              Data.Ix
import              Data.STRef
import              Data.IORef
import              GHC.Err
import              Control.Monad
import              Control.Monad.ST
import              Data.Either
import              Data.Char
import              System.IO
import              Control.DeepSeq
import              GHC.Generics                    (Generic, Generic1)
import qualified    Data.Attoparsec.Text            as DAT
import              Data.Attoparsec.Text
import              Control.Applicative
import              Control.Monad.IO.Class          (liftIO, MonadIO)
import              Control.Monad.Trans.Resource.Internal
import              Debug.Trace
import              Text.Show.Unicode               (ushow)

-- conduit
import              Data.Conduit
import qualified    Data.Conduit.List               as CL
import qualified    Data.Conduit.Binary             as CB hiding (sequence, dropWhile, sourceFile)
import qualified    Data.Conduit.Combinators        as CC


--  for pararel
import              Control.Parallel.Strategies     hiding (parMap, (.|))
import              Control.Parallel
import qualified    Control.Monad.Parallel          as CMP

--  Original Modules
import qualified    CSV.Text                        as CSV
import              CSV.Text


-- Directory
import qualified    System.Directory                as SD

------------------------------------------------------------
-- * General Functions
------------------------------------------------------------

type Year = Int


-- | デバッグ用のMap.lookup
lookupErr :: (Ord a, Show a) =>  a -> Map a b -> b
lookupErr x th = case (Map.lookup x th) of
                     Just a  -> a
                     Nothing -> error $ "Can not transrate \"" ++ ushow x  ++ "\""


------------------------------------------------------------------
-- ** For Parallel
-----------------------------------------------------------

-- | Parallel map
parMap :: (a -> b) -> [a] -> Eval [b]
parMap f [] = return []
parMap f !(a:as)  = do
    b  <- rpar (f a)
    bs <- parMap f as
    return (b:bs)

-- | Parallel Map Strict
parMapStrict :: NFData b => (a -> b) -> [a] -> Eval [b]
parMapStrict f [] = return []
parMapStrict f !(a:as)  = do
    ! b  <- rpar (f a)
    ! bs <- b `deepseq` parMap f as
    return  (b:bs)


-- |  Parallel mapM_
parMapM_ f xs = sequence_ $ runEval $ parMap f xs

parMapM f xs = sequence $ runEval $ parMap f xs

-- |  Parallel forM_ only for ST
parForMST_ ::  [a] -> (a -> ST s a1) -> ST s ()
parForMST_ = flip parMapM_

-- |  Parallel forM_ only for IO
parForMIO_ :: [a] -> (a -> IO a1) -> IO ()
parForMIO_ = flip parMapM_


multi :: (a -> a) -> Int -> (a -> a)
multi f 1 = f
multi f n | n <= 0    =  error "multipled minus"
          | otherwise =  f.(multi f (n-1))


-- ** For fast Read
-----------------------------------------------------------

{-# INLINE fastReadInt #-}
fastReadInt :: String -> Int
fastReadInt s = case N.readDec s of
            [(n,"")] -> n
            x        -> error $ "fastReadInt error ;" ++ ushow x

{-# INLINE fastReadDouble #-}
fastReadDouble :: String -> Double
fastReadDouble s = case N.readFloat s of
                [(n,"")] -> n
                x        -> error $ "fastReadDouble error ;" ++ ushow x

noneOf cs           = satisfy (\c -> not (elem c cs))


{-# INLINE cell #-}
cell = (quotedCell <|> many' (noneOf ",\n\r")) >>= (\res -> return $! T.pack res)

{-# INLINE quotedCell #-}
quotedCell  =  char  '"'
            >> many' quotedChar >>= \content
            -> (char '"' <?> "quote at end of cell")
            >> return content
{-# INLINE quotedChar #-}
quotedChar =  noneOf "\""
          <|> try (string  (T.pack "\"\"") >> return '"')



------------------------------------------------------------
--  * File Information
------------------------------------------------------------
{- | ファイル形式
経済センサスのデータは調査票別年度別(24,28年)に32種類に分類される.
センサスデータを読み込むための情報
センサスのヘッダーを総務省，経産省ともにすべて統一する
-}
data FileType   = SB28  {- ^ 28年共通項目   -} | SC28  {- ^ 28年農林漁業      -} | SD28  {- ^ 28年鉱業       -}
                | SE28  {- ^ 28年製造業     -} | SG28  {- ^ 28年商業          -} | SH28  {- ^ 28年医療福祉   -}
                | SJ28  {- ^ 28年学校教育   -} | SK28  {- ^ 28年建設サービスA -} | SM28  {- ^ 28年サービスB  -}
                | SB24  {- ^ 24年共通項目   -} | SC24  {- ^ 24年農林漁業      -} | SD24  {- ^ 24年鉱業       -}
                | SE24  {- ^ 24年製造業     -} | SG24  {- ^ 24年商業          -} | SH24  {- ^ 24年医療福祉   -}
                | SJ24  {- ^ 24年学校教育   -} | SK24  {- ^ 24年建設サービスA -} | SM24  {- ^ 24年サービスB  -}
                | KC28  {- ^ 28年商業       -} | KM28  {- ^ 28年鉱業          -} | K24   {- ^ 24年全て       -}
                | K28   {- ^ 28年全て       -} | KMI28 {- ^ 28年製造業産業    -} | KMP28 {- ^ 28年製造業品目 -}

                deriving (Eq, Show, Enum)

-- | データの提供元
data Dep = S  -- ^ 総務省
         | K  -- ^ 経産省
         deriving (Eq,Show)




-- | データの対象年度を返す
getFileYear :: FileType -> Year
getFileYear = f
    where
    f SB24 = 24 ; f SC24 = 24 ; f SD24 = 24
    f SE24 = 24 ; f SG24 = 24 ; f SH24 = 24
    f SJ24 = 24 ; f SK24 = 24 ; f SM24 = 24
    f K24  = 24 ; f _    = 28


-- | データの提供元を返す
getFileDep :: FileType -> Dep
getFileDep = f
    where
        f KC28  = K ; f KM28  = K ; f KMI28 = K
        f KMP28 = K ; f K24   = K ; f K28   = K
        f _     = S


-- | データの対象産業を返す
getFileInd :: FileType -> E対象産業
getFileInd = f
    where
    f SB28  = E共通     ; f SC28 = E農林漁業      ; f SD28  = E鉱業
    f SE28  = E製造業   ; f SG28 = E商業          ; f SH28  = E医療福祉
    f SJ28  = E学校教育 ; f SK28 = E建設サービスA ; f SM28  = EサービスB
    f SB24  = E共通     ; f SC24 = E農林漁業      ; f SD24  = E鉱業
    f SE24  = E製造業   ; f SG24 = E商業          ; f SH24  = E医療福祉
    f SJ24  = E学校教育 ; f SK24 = E建設サービスA ; f SM24  = EサービスB
    f KC28  = E商業     ; f KM28 = E鉱業          ; f KMI28 = E製造業
    f KMP28 = E製造業   ; f K24  = E全産業        ; f K28   = E全産業


-- | データのパスを返す

getRecordFilePath :: FileType -> String
getRecordFilePath = f
    where
    f  SB28  =  "Data/Record/" ++ show  SB28  ++ ".csv"   --  28年共通項目
    f  SC28  =  "Data/Record/" ++ show  SC28  ++ ".csv"   --  28年農林漁業
    f  SD28  =  "Data/Record/" ++ show  SD28  ++ ".csv"   --  28年鉱業
    f  SE28  =  "Data/Record/" ++ show  SE28  ++ ".csv"   --  28年製造業
    f  SG28  =  "Data/Record/" ++ show  SG28  ++ ".csv"   --  28年商業
    f  SH28  =  "Data/Record/" ++ show  SH28  ++ ".csv"   --  28年医療福祉
    f  SJ28  =  "Data/Record/" ++ show  SJ28  ++ ".csv"   --  28年学校教育
    f  SK28  =  "Data/Record/" ++ show  SK28  ++ ".csv"   --  28年建設サービスA
    f  SM28  =  "Data/Record/" ++ show  SM28  ++ ".csv"   --  28年サービスB
    f  SB24  =  "Data/Record/" ++ show  SB24  ++ ".csv"   --  24年共通項目
    f  SC24  =  "Data/Record/" ++ show  SC24  ++ ".csv"   --  24年農林漁業
    f  SD24  =  "Data/Record/" ++ show  SD24  ++ ".csv"   --  24年鉱業
    f  SE24  =  "Data/Record/" ++ show  SE24  ++ ".csv"   --  24年製造業
    f  SG24  =  "Data/Record/" ++ show  SG24  ++ ".csv"   --  24年商業
    f  SH24  =  "Data/Record/" ++ show  SH24  ++ ".csv"   --  24年医療福祉
    f  SJ24  =  "Data/Record/" ++ show  SJ24  ++ ".csv"   --  24年学校教育
    f  SK24  =  "Data/Record/" ++ show  SK24  ++ ".csv"   --  24年建設サービスA
    f  SM24  =  "Data/Record/" ++ show  SM24  ++ ".csv"   --  24年サービスB
    f  K24   =  "Data/Record/" ++ show  K24   ++ ".csv"
    f  K28   =  "Data/Record/" ++ show  K28   ++ ".csv"
    f  KM28  =  "Data/Record/" ++ show  KM28  ++ ".csv"
    f  KC28  =  "Data/Record/" ++ show  KC28  ++ ".csv"
    f  KMI28  = "Data/Record/" ++ show  KMI28 ++ ".csv"
    f  KMP28  = "Data/Record/" ++ show  KMP28 ++ ".csv"




------------------------------------------------------------------
-- * Header
------------------------------------------------------------------

-- | Original Data のHeader情報
type RecordHeader  = Text

-- | FileType をもとにHeader情報を取得する
{-# INLINE getHeader #-}
getHeader :: FileType -> [RecordHeader]
getHeader = f
    where
    f SB28  = hSB28 ; f SC28  = hSC28  ; f SD28  = hSD28
    f SE28  = hSE28 ; f SG28  = hSG28  ; f SH28  = hSH28
    f SJ28  = hSJ28 ; f SK28  = hSK28  ; f SM28  = hSM28
    f SB24  = hSB24 ; f SC24  = hSC24  ; f SD24  = hSD24
    f SE24  = hSE24 ; f SG24  = hSG24  ; f SH24  = hSH24
    f SJ24  = hSJ24 ; f SK24  = hSK24  ; f SM24  = hSM24
    f K28   = hK28  ; f K24   = hK24   ; f KC28  = hKC28
    f KM28  = hKM28 ; f KMI28 = hKMI28 ; f KMP28 = hKMP28


-- TemplateHaskell でコンパイル時読み込み
hSB28   = CSV.getSingleCol $( loadCSV "Data/Header/hSB28.csv")  ; hSC28   = getSingleCol $( loadCSV "Data/Header/hSC28.csv")
hSD28   = CSV.getSingleCol $( loadCSV "Data/Header/hSD28.csv")  ; hSE28   = getSingleCol $( loadCSV "Data/Header/hSE28.csv")
hSG28   = CSV.getSingleCol $( loadCSV "Data/Header/hSG28.csv")  ; hSH28   = getSingleCol $( loadCSV "Data/Header/hSH28.csv")
hSJ28   = CSV.getSingleCol $( loadCSV "Data/Header/hSJ28.csv")  ; hSK28   = getSingleCol $( loadCSV "Data/Header/hSK28.csv")
hSM28   = CSV.getSingleCol $( loadCSV "Data/Header/hSM28.csv")  ; hSB24   = getSingleCol $( loadCSV "Data/Header/hSB24.csv")
hSC24   = CSV.getSingleCol $( loadCSV "Data/Header/hSC24.csv")  ; hSD24   = getSingleCol $( loadCSV "Data/Header/hSD24.csv")
hSE24   = CSV.getSingleCol $( loadCSV "Data/Header/hSE24.csv")  ; hSG24   = getSingleCol $( loadCSV "Data/Header/hSG24.csv")
hSH24   = CSV.getSingleCol $( loadCSV "Data/Header/hSH24.csv")  ; hSJ24   = getSingleCol $( loadCSV "Data/Header/hSJ24.csv")
hSK24   = CSV.getSingleCol $( loadCSV "Data/Header/hSK24.csv")  ; hSM24   = getSingleCol $( loadCSV "Data/Header/hSM24.csv")
hK28    = CSV.getSingleCol $( loadCSV "Data/Header/hK28.csv" )  ; hK24    = getSingleCol $( loadCSV "Data/Header/hK24.csv" )
hKC28   = CSV.getSingleCol $( loadCSV "Data/Header/hKC28.csv")  ; hKM28   = getSingleCol $( loadCSV "Data/Header/hKM28.csv")
hKMI28  = CSV.getSingleCol $( loadCSV "Data/Header/hKMI28.csv") ; hKMP28  = getSingleCol $( loadCSV "Data/Header/hKMP28.csv")


-- | Fileの末尾を書き換えてConverted.csvのPathを得る
originalToConverted :: FilePath -> FilePath
originalToConverted fp = (init.init.init.init) fp ++ "Converted.csv"


-- | テストデータ使うときに便利
originalToForTest :: FilePath -> FilePath
originalToForTest fp = (init.init.init.init) fp ++ "ForTest.csv"

-- | ソート済みファイル名に変換
originalToSorted :: FilePath -> FilePath
originalToSorted fp = (init.init.init.init) fp ++ "Sorted.csv"



-- ** Data input, output
------------------------------------------------------------------

type RowS    = Vector String
type ColS    = Vector String
type MatrixS = Vector (Vector String)

type RowT    = Vector Text
type ColT    = Vector Text
type MatrixT = Vector (Vector Text)


transposeV :: MatrixT -> MatrixT
transposeV mx = V.fromList $ runEval$ parMap (indicesV mx) $ [0..(lenLineV mx)]

lenLineV :: MatrixT -> Int
lenLineV line = V.foldl1 max $ V.map V.length line

indicesV :: MatrixT -> Int -> RowT
indicesV xs i = V.map (\x -> if (V.length x) > i then x V.! i else T.empty) xs

transpose :: [[Text]] -> [[Text]]
transpose mx = runEval $ parMap (VTable.Data.Structure.indices mx) $ [0..(lenLine mx)]

lenLine :: [[Text]] -> Int
lenLine line = L.maximum $ L.map L.length line

indices :: [[Text]] -> Int -> [Text]
indices xs i = L.map (\x -> if (L.length x) > i then x !! i else T.empty) xs


toMap :: MatrixS -> Either String (Map.Map String String)
toMap mx
    | (V.length mx) /= 2 = Left "MatrixS should has only 2 columns."
    | otherwise = Right $ Map.fromList $ V.toList
                        $ V.zip (mx V.! 0) (mx V.! 1)


trim :: String -> String
trim = f . f
    where f = reverse . dropWhile isSpace

isBlank :: String -> Bool
isBlank str  = L.and $ L.map isSpace str

-- | nub
mergenub :: (Ord a, Eq a) => [a] -> Eval [a]
mergenub []     = return []
mergenub (x:[]) = return [x]
mergenub !xs    =  mergenub ys  >>= \ys'
                -> mergenub zs  >>= \zs'
                -> ys' `par` zs' `pseq` return $! merge ys' zs'
    where
        (ys, zs) = halve xs
        merge :: (Ord a, Eq a) => [a] -> [a] -> [a]
        merge [] [] = []
        merge [] y  = y
        merge x []  = x
        merge !(x:xs) !(y:ys)
            | x < y     = [x] ++ merge xs (y:ys)
            | x == y    = [x] ++ merge xs ys
            | otherwise = [y] ++ merge (x:xs) ys

        halve !xs = let len = (L.length xs) `div` 2
                  in (L.take len xs, L.drop len xs)

------------------------------------------------------------------
-- * データの統合
------------------------------------------------------------------
type InputFile  = FilePath
type OutputFile = FilePath
type TempFile   = FilePath

-- | 異なるファイルの同じ事業所を統合する
-- * 全事業所の番号を取得する
-- * それを与えて,Arrayに全て入れ,Nullを潰していく
-- * 重複を更新し,最終的なArrayをCsvに出力
-- 速いが全てのテーブルを読み込むためメモリが足りない

mergeFiles :: OutputFile -> Year ->  IO ()
mergeFiles filepath year = do
    esIdxes <- collectAllEstIdx files

    let ! maxIC = toInteger $ (length esIdxes) - 1
        ! esIdxICMap = Map.fromList $ zip esIdxes [0..maxIC]

    arr     <- newArray ((H直轄企業コード,0),(H事業所別生産物別売上高,maxIC)) Null :: IO IOCensusData
    print "start to merge"

    CMP.forM_ files $ \file -> do
            print $ "dealing " ++ file
            withFile file ReadMode $ \rHandle
                -> TO.hGetLine rHandle >>= \ln
                -> let !headers = Map.fromList (L.zip (L.map parseHeader ((L.head . parseCSVErr) ln)) [0..])
                in loop arr esIdxICMap headers rHandle
            print $ "finish " ++ file

    print $ "now writing" ++ filepath
    writeIOCensus filepath arr
    print "finished!"

    where
    files = map (originalToConverted . getRecordFilePath) $ L.filter (\x -> getFileYear x == year)  [SB28 .. KMP28]
    loop :: IOCensusData -> Map Text IC -> Map Header Int -> Handle -> IO ()
    loop arr esIdxICMap headers rHandle
        = hIsEOF rHandle >>= \eof
        -> case eof of
            True   ->   return ()
            False  ->   head <$> parseCSVErr <$> TO.hGetLine rHandle >>= \ line
                        ->  let !estIdx = readDataWithMap H直轄企業コード headers line
                        in case  (estIdx /= Null) of
                            True    -> CMP.forM_ [H直轄企業コード ..  H金融業保険業の事業種類] ( \hd
                                                    -> let !val = readDataWithMap hd headers line
                                                    in let !ic  = Maybe.fromJust (Map.lookup (text estIdx) esIdxICMap)
                                                    in when (val /= Null) (writeArray arr (hd,ic) val))
                                    >> loop arr esIdxICMap headers rHandle
                            False   -> loop arr esIdxICMap headers rHandle


{- | メモリ効率の良い版
     各ファイルをソートしたのち，
     事業所番号でファイル全体をマージソートして出力
     上から順に処理して,同じ行がなくなったら出力


     分割してクイックマージにする
     Conduitで全ファイル同時に読み込んで処理する
        など別の方法で高速化したほうが良い.

-}



mergeFilesMemEfficient :: OutputFile -> Year -> IO ()
mergeFilesMemEfficient outputFile year
    = let files   = map (originalToConverted . getRecordFilePath)
                        (L.filter (\x -> getFileYear x == year)  [SB28 .. KMP28])
    in print "start sorting files ..." >>  CMP.forM files sortFile
    >> let sortedFiles = map originalToSorted files
    in case year of
            24 -> print "start merging files ..."
               >> withFile "tempFile.csv" WriteMode (\ h -> TO.hPutStrLn h outputHeader
                                                         >> CSV.hPutCsvLn h (L.replicate (L.length headerList) (T.pack "Null")))
               >> merge outputFile ("tempFile.csv", sortedFiles)
               >> return ()

            _  -> error "procedure for 28 is not defined"

    where
    --
    merge :: OutputFile -> (TempFile, [InputFile]) -> IO (TempFile, [InputFile])
    merge outputFile (tempFile, [])     =  SD.copyFile tempFile outputFile
                                        >> SD.removeFile tempFile
                                        >> return (outputFile, [])

    merge outputFile (tempFile, x:[])   =  merge2Files tempFile x >>= \ newTempFile
                                        -> SD.copyFile newTempFile outputFile
                                        >> SD.removeFile newTempFile
                                        >> return (outputFile, [])

    merge outputFile (tempFile, x:xs)   =  print ((show (length xs)) ++ " files left ...")
                                        >> merge2Files tempFile x >>= \ newTempFile
                                        -> merge  outputFile (newTempFile, xs)

    {-# INLINE merge2Files #-}
    merge2Files :: InputFile -> InputFile -> IO OutputFile
    merge2Files inpFst inpSnd = do

        rHandleFst  <- openFile inpFst ReadMode
        hdFst       <- TO.hGetLine rHandleFst
        let !hdMapFst = Map.fromList (L.zip (L.map parseHeader ((L.head . parseCSVErr) hdFst)) [0..1000])

        rHandleSnd  <- openFile inpSnd ReadMode
        hdSnd       <- TO.hGetLine rHandleSnd
        let !hdMapSnd = Map.fromList (L.zip (L.map parseHeader ((L.head . parseCSVErr) hdSnd)) [0..1000])

        let  newOutputFile = (init.init.init.init) inpFst ++ "again.csv"
        wHandle     <- openFile newOutputFile WriteMode -- againが末尾に追加された中間ファイルがどんどんできてくる
        TO.hPutStrLn wHandle outputHeader

        maybeLineFst     <- Just <$> head <$> parseCSVErr <$> TO.hGetLine rHandleFst
        maybeLineSnd     <- Just <$> head <$> parseCSVErr <$> TO.hGetLine rHandleSnd

        firstIOCensus    <- (newArray (H直轄企業コード, H事業所別生産物別売上高) Null :: IO IOCensusRow)

        loop rHandleFst rHandleSnd wHandle maybeLineFst maybeLineSnd hdMapFst hdMapSnd firstIOCensus
        mapM_ hClose [wHandle, rHandleFst, rHandleSnd]
        SD.removeFile inpFst
        return newOutputFile


    {-# INLINE loop #-}
    loop :: Handle          {- ^ rHandleFst -}
         -> Handle          {- ^ rHandleSnd -}
         -> Handle          {- ^ wHandle -}
         -> Maybe [Text]    {- ^ Maybe lineFst -}
         -> Maybe [Text]    {- ^ Maybe lineSnd -}
         -> Map Header Int  {- ^ hdFst -}
         -> Map Header Int  {- ^ hdSnd -}
         -> IOCensusRow     {- ^ current array -}
         -> IO ()
    loop rHandleFst rHandleSnd wHandle maybeLineFst maybeLineSnd hdMapFst hdMapSnd currentIOCensus
        =   case (maybeLineFst, maybeLineSnd) of
            (Nothing, Nothing)              -> forM headerList (\ !hd -> T.pack . ushow <$> readArray currentIOCensus hd) >>= \outputLine
                                            -> CSV.hPutCsvLn wHandle outputLine
                                            >> return ()

            (Just lineFst, Nothing)         -> readAndWrite lineFst hdMapFst rHandleFst wHandle LT currentIOCensus

            (Nothing,      Just lineSnd)    -> readAndWrite lineSnd hdMapSnd rHandleSnd wHandle GT currentIOCensus

            (Just lineFst, Just lineSnd)    -> case compareLine lineFst hdMapFst lineSnd hdMapSnd of
                                                    LT  -> readAndWrite lineFst hdMapFst rHandleFst wHandle LT currentIOCensus
                                                    GT  -> readAndWrite lineSnd hdMapSnd rHandleSnd wHandle GT currentIOCensus

            where

            {-# INLINE readAndWrite #-}
            readAndWrite    :: [Text]           {- ^ lineFst pr lineSnd -}
                            -> Map Header Int   {- ^ hdFst or hdSnd-}
                            -> Handle           {- ^ rHadleFst or rHandleSnd -}
                            -> Handle           {- ^ wHandle -}
                            -> Ordering
                            -> IOCensusRow      {- ^ current array -}
                            -> IO ()

            readAndWrite line hdMap rHandle wHandle ord currentIOCensus
                =  readArray currentIOCensus H事業所番号 >>= \currentId
                -> let tempId    = readDataWithMap H事業所番号 hdMap line
                in let hdlist    = Map.keys hdMap
                in case (tempId == currentId) of
                    True    -> forM_ hdlist ( \hd -> let !val = readDataWithMap hd hdMap line
                                                     in when (val /= Null) (writeArray currentIOCensus hd val)) {- IOCensus を統合して書き込まず次に進む-}
                            >> hIsEOF rHandle >>= \ eof
                            -> case eof  of
                                True    -> case ord of
                                            LT -> loop rHandleFst rHandleSnd wHandle Nothing      maybeLineSnd hdMapFst hdMapSnd currentIOCensus
                                            GT -> loop rHandleFst rHandleSnd wHandle maybeLineFst Nothing      hdMapFst hdMapSnd currentIOCensus

                                False   -> head <$> parseCSVErr <$> TO.hGetLine rHandle >>= \ newLine
                                        -> case ord of
                                            LT -> loop rHandleFst rHandleSnd wHandle (Just newLine) maybeLineSnd   hdMapFst hdMapSnd currentIOCensus
                                            GT -> loop rHandleFst rHandleSnd wHandle maybeLineFst   (Just newLine) hdMapFst hdMapSnd currentIOCensus

                    False   -> forM headerList (\ !hd -> T.pack . ushow <$> readArray currentIOCensus hd) >>= \currentOutputLine {- IOCensus 書き込んだ後更新 -}
                            -> CSV.hPutCsvLn wHandle currentOutputLine
                            >> (newArray (H直轄企業コード, H事業所別生産物別売上高) Null :: IO IOCensusRow) >>= \ newIOCensus
                            -> forM_ hdlist ( \hd -> let !val = readDataWithMap hd hdMap line
                                                     in when (val /= Null) (writeArray newIOCensus hd val))
                            >> hIsEOF rHandle >>= \ eof
                            -> case eof  of
                                True    -> case ord of
                                            LT -> loop rHandleFst rHandleSnd wHandle Nothing      maybeLineSnd hdMapFst hdMapSnd newIOCensus
                                            GT -> loop rHandleFst rHandleSnd wHandle maybeLineFst Nothing      hdMapFst hdMapSnd newIOCensus

                                False   -> head <$> parseCSVErr <$> TO.hGetLine rHandle >>= \ newLine
                                        -> case ord of
                                            LT -> loop rHandleFst rHandleSnd wHandle (Just newLine) maybeLineSnd   hdMapFst hdMapSnd newIOCensus
                                            GT -> loop rHandleFst rHandleSnd wHandle maybeLineFst   (Just newLine) hdMapFst hdMapSnd newIOCensus


    -- 2つのIOCensusRow のうち直轄企業コードが小さい方(1か2)を返す
    {-# INLINE compareLine #-}
    compareLine :: [Text]           {- ^ lineFst -}
                -> Map Header Int   {- ^ hdFst -}
                -> [Text]           {- ^ lineSnd -}
                -> Map Header Int   {- ^ hdSnd -}
                -> Ordering
    compareLine  lineFst hdFst lineSnd hdSnd
        =  case compare (textWithNull (readDataWithMap H直轄企業コード hdFst lineFst)) (textWithNull (readDataWithMap H直轄企業コード hdSnd lineSnd)) of
                LT  -> LT
                EQ  -> LT
                GT  -> GT

{- | それぞれのファイルを事業所番号でソートする
    配列に読み込んで,直轄企業コードのみ抜き出しソート,インデックスを処理
    出力ファイル名は自動で,末尾 "Sorted.csv"になる.

-}

sortFile :: InputFile  -> IO ()
sortFile input  =  readCensus input >>= \censusData
                -> let sortedIndex  =  L.map fileIndex $ L.sort $ (flip L.map) [0 .. (snd . snd . bounds) censusData]
                                    $ \x -> ForSortFile x $ textWithNull $ censusData ! (H事業所番号, x)
                in withFile (originalToSorted input) WriteMode $ \ wHandle
                        -> TO.hPutStrLn wHandle outputHeader
                        >> forM_ sortedIndex ( \num
                            -> CSV.hPutCsvLn wHandle
                            $ (flip  map) headerList $ \h
                                ->  T.pack . ushow $ censusData ! (h, num))



-- | ソート用に作ったOrdの異なったTurple
data ForSortFile = ForSortFile  { fileIndex :: {-# UNPACK #-} !Integer
                                , enid      :: {-# UNPACK #-} !T.Text } deriving (Show, Eq)

instance Ord ForSortFile where
    compare   x y     = compare   (enid x) (enid y)
    (<)       x y     = (<)       (enid x) (enid y)
    (<=)      x y     = (<=)      (enid x) (enid y)
    (>)       x y     = (>)       (enid x) (enid y)
    (>=)      x y     = (>=)      (enid x) (enid y)
    max x y | x >= y    = x
            | otherwise = y

    min x y | x <= y    = x
            | otherwise = y


{-

mergeFiles :: FilePath -> Year -> IO ()
mergeFiles outputFile year = do
    esIdxes <- collectAllEstIdx files
    let maxCount = fromIntegral (L.length esIdxes) :: Double
    print "merging files ..."
    withFile outputFile WriteMode $ \ !wHandle -> do
        TO.hPutStrLn wHandle outputHeader
        !count <- newIORef 0.0 :: IO (IORef Double)
        CMP.forM_ esIdxes $ \ !idx -> do
            modifyIORef count (1 + )
            !currentCount <- readIORef count
            let !progress = "   Progress : " ++ show (100 * currentCount / maxCount) ++ " % \r"
            putStr progress >> hFlush stdout

            !icr <- newArray (H直轄企業コード,H事業所別生産物別売上高) Null :: IO IOCensusRow
            CMP.forM_ files ( \ !file -> do
                    withFile file ReadMode ( \ !rHandle -> do
                        !firstLine <- TO.hGetLine rHandle
                        let !headers = Map.fromList (L.zip (L.map parseHeader ((L.head . parseCSVErr) firstLine)) [0..])
                        loop rHandle idx icr headers))

            resultRow <- mapM (\hd -> T.pack <$> ushow <$> (readArray icr hd)) headerList
            let !tx = (T.concat . (L.intersperse (T.pack ",")).(L.map toCsvText)) resultRow
            TO.hPutStr wHandle tx
    where
    files = map (originalToConverted . getRecordFilePath) $ L.filter (\x -> getFileYear x == year)  [SB28 .. KMP28]
    loop :: Handle -> Text -> IOCensusRow -> Map Header Int -> IO ()
    loop !rHandle !idx !icr !headers
        = hIsEOF rHandle >>= \ eof
        -> case eof of
            True   ->   return ()
            False  ->   head <$> parseCSVErr <$> TO.hGetLine rHandle >>= \ line
                        ->  let !valRedIdx = readDataWithMap H事業所番号 headers line
                        in  case valRedIdx of
                                Null           -> loop rHandle idx icr headers
                                VText redIdx   -> case (redIdx == idx) of
                                                    False -> loop rHandle idx icr headers
                                                    True  -> do  CMP.forM_ [H直轄企業コード ..  H金融業保険業の事業種類]
                                                                        (\ hd -> do
                                                                            let !val = readDataWithMap hd headers line
                                                                            case val of
                                                                                Null -> return ()
                                                                                _    -> writeArray icr hd val )

-}

------------------------------------------------------------
-- * Cesnsus Data
------------------------------------------------------------

-- | Identification Code
--  識別コード　直轄企業コードとは別に,全ての行のインデックスでマトリックスを作る
type IC = Integer
type Cell = (Header,IC)

-- | 整理されたデータの形態
-- * データテーブルの形で,Header × IC
--
--  メモリのことを考えると,DBの方が良いのだが,初期環境の問題で,こうなっている.
--
--  完全にサンクコストなので,修正したほうがよい.
--  IMutableArray CensusData
type CensusData = Array Cell Val

-- | MutableArray版のCensusData
type STCensusData s = STArray s Cell Val
type IOCensusData = IOArray Cell Val

-- | Stream 用の CensusData
type CensusRow   = Array   Header Val
type IOCensusRow = IOArray Header Val

-- | テーブルから要素を抽出する関数
proj :: CensusData -> Cell ->  Val
proj d c  = d ! c



------------------------------------------------------------------
--  ** 変換された Census Data からの読み書き処理
------------------------------------------------------------------

-- | CensusData <-> CSV の変換を定義する
--
--   Header を指定して指定されたデータを読み込む
{-# INLINE readData #-}
readData :: Header -> [Header] -> [Text] -> Val
readData !x !hds !xs   =  let !tx = projHd x hds xs
                       in parseVal tx

    where
    projHd :: Header -> [Header] -> [Text] -> Text
    projHd hd hds tx =  case L.elemIndex hd hds of
                        Just x  -> if (length tx - 1) >= x  then (L.!!) tx x
                                                            else error $ "In the function readData: Can not project hd \""
                                                                    ++ (ushow hd)  ++ "\" line is too short"
                                                                    ++ ushow tx
                        Nothing -> error  $ "In the function readData:  Can not project hd \""
                                        ++ (ushow) hd  ++ "\" in \r\n"
                                        ++ ushow hds


-- | CensusData <-> CSV の変換を定義する
--
--   最適化用のHeaderをMapにしたバージョン

{-# INLINE readDataWithMap #-}
readDataWithMap :: Header -> Map Header Int  -> [Text] -> Val
readDataWithMap !hd !hds !xs   =  let !tx = projHd hd hds xs
                          in parseVal tx

    where
    projHd :: Header -> Map Header Int -> [Text] -> Text
    projHd hd hds tx =  case Map.lookup hd hds of
                        Just x  | (length tx - 1) >= x  -> (L.!!) tx x
                                | otherwise             -> error    $  "In the function readDataWithMap : Can not project hd \""
                                                                    ++ (ushow hd)  ++ "\" line is too short"
                                                                    ++ ushow tx
                        Nothing -> error  $ "In the function readDataWithMap : Can not project hd \""
                                        ++ (ushow) hd  ++ "\" in \r\n"
                                        ++ ushow hds




writeCensus :: FilePath -> CensusData -> IO ()
writeCensus filePath cd = do
        let maxNum = (snd.snd) $ bounds cd

        wHandle <- openFile filePath WriteMode
        TO.hPutStrLn wHandle outputHeader

        forM_ [0 .. maxNum] $ \num -> do
            let line = L.map (\hd -> (T.pack . show) (cd ! (hd,num) )) headerList
            CSV.hPutCsvLn wHandle line

        hClose wHandle

writeIOCensus :: FilePath -> IOCensusData -> IO ()
writeIOCensus filePath icd  = do
        !maxNum  <- (snd.snd) <$> getBounds icd
        !wHandle <- openFile filePath WriteMode
        TO.hPutStrLn wHandle outputHeader
        forM_ [0 .. maxNum] $ \num -> do
                !line <- forM headerList (\ !hd -> T.pack . show <$> readArray icd (hd, num))
                CSV.hPutCsvLn wHandle line

        hClose wHandle


readIOCensus :: FilePath -> IO IOCensusData
readIOCensus filePath = do
        !num     <- toInteger. L.length . T.lines <$> TO.readFile filePath
        !file    <- readCSV filePath
        !idx     <- newIORef 0
        let !headers = L.map parseHeader $ L.head file
        arr     <- newArray ((H直轄企業コード, 0),(H事業所別生産物別売上高, num)) Null :: IO IOCensusData
        CMP.forM_ (tail file) ( \line -> do
            CMP.forM_ headers ( \h ->  do
                let val = readData h headers line
                tempNum <- readIORef idx
                writeArray arr (h,tempNum) val)
            modifyIORef idx (+ 1))
        return arr


-- | FileをすべてArray :: CensusData で読み込む
readCensus :: InputFile -> IO CensusData
readCensus input = do
        !num     <- toInteger. L.length . T.lines <$> TO.readFile input
        !file    <- readCSV input
        !idx     <- newIORef 0
        let hdList = L.map parseHeader $ L.head file
            hdMap  = Map.fromList $ L.zip hdList [0 .. ]
        !arr     <- newArray ((H直轄企業コード, 0),(H事業所別生産物別売上高, num)) Null :: IO IOCensusData
        CMP.forM_ (tail file) $ \ !line -> do
            forM_ hdList $ \h ->  do
                let !val = readDataWithMap h hdMap line
                !tempNum <- readIORef idx
                val `deepseq` writeArray arr (h,tempNum) val
            modifyIORef idx (+ 1)
        !result <- freeze arr :: IO CensusData
        return result



-- | ファイルからデータを取ってきて,censusRowにするSorce
--
--   メモリ消費は低いが逐次処理しかできないかつ，遅い
{-# INLINE sourceCensus #-}
sourceCensus :: MonadResource m =>  FilePath -> ConduitT a IOCensusRow m ()
sourceCensus input  =  CC.sourceFile input      .| CB.lines
                                                .| CL.map E.decodeUtf8
                                                .| text2IOCensusRow 0 (Map.empty)

-- | Textを受け取って，IOCensusRowに変換するConduit
{-# INLINE text2IOCensusRow #-}
text2IOCensusRow :: (Monad m, MonadIO m ) => Integer -> Map Header Int -> ConduitT Text IOCensusRow m ()
text2IOCensusRow n hd
    | n == 0    =  await >>= \ firstLine
                -> case firstLine of
                    Nothing     -> return ()
                    Just line   ->  let !hdMap = makeHeadMap line
                                    in await >>= \ !sndLine
                                    -> case sndLine of
                                            Nothing     -> return ()
                                            Just line2  -> liftIO (g hdMap line2) >>= \ !result
                                                        -> yield result
                                                        >> text2IOCensusRow (n + 1) hdMap

    | otherwise =  await >>= \ tailLine
                -> case tailLine of
                    Nothing   -> return ()
                    Just line -> liftIO (g hd line) >>= \ !result
                              -> yield result
                              >> text2IOCensusRow (n + 1) hd
    where
    makeHeadMap hd = Map.fromList (L.zip (L.map parseHeader ((L.head . parseCSVErr) hd)) [0 ..])

    g :: Map Header Int -> Text -> IO IOCensusRow
    g hd line = do  arr  <- newArray (H直轄企業コード, H事業所別生産物別売上高) Null :: IO IOCensusRow
                    CMP.forM_ headerList $ \ !h ->  do
                        let !val = readDataWithMap h hd ((L.head . parseCSVErr) line)
                        val `deepseq` writeArray arr h val
                    return arr


-- | IOCensusRowを出力するSink
--
--  Double はファイルの最大行数,進捗率を計算する
{-
sinkCensus :: MonadResource m => Double -> FilePath -> ConduitT IOCensusRow Void m ()
sinkCensus !maxRowNum !outputFile = ioCensusRow2Text maxRowNum 0    .| CL.map (E.encodeUtf8 . T.toStrict)
                                                                    .| CC.unlinesAscii
                                                                    .| CC.sinkFile outputFile
-}

{-# INLINE sinkCensus#-}
sinkCensus :: MonadResource m => Double -> FilePath -> ConduitT IOCensusRow Void m ()
sinkCensus !maxRowNum !outputFile
    =  liftIO (openFile outputFile WriteMode) >>= \wHandle
    -> ioCensusRow2Text maxRowNum 0 .| unlinesTL .| sinkFileTL wHandle


{-# INLINE sinkFileTL #-}
sinkFileTL ::(MonadIO m) =>  Handle ->  ConduitT Text Void m ()
sinkFileTL wHandle =  await >>= \maybeTx
           -> case maybeTx of
                Nothing -> liftIO (hClose wHandle) >> return ()
                Just tx -> liftIO (TO.hPutStr wHandle tx)
                        >> sinkFileTL wHandle

-- | IOCensusRowを受け取ってTextにするConduit

{-# INLINE ioCensusRow2Text #-}
ioCensusRow2Text :: (Monad m, MonadIO m) => Double -> Integer ->  ConduitT IOCensusRow Text m ()
ioCensusRow2Text !maxRowNum !num    | num == 0  = yield outputHeader >> f maxRowNum (num + 1)
                                    | otherwise = f maxRowNum num
    where
    f !maxRowNum !num = do
        maybeIcd <- await
        case maybeIcd of
            Nothing   -> liftIO (print "finished") >>  return ()
            Just icd  -> liftIO (forM headerList (\ hd ->  T.pack <$> show <$> (readArray icd hd)))
                      >>= \ result
                      -> let tx = (T.concat . (L.intersperse (T.pack ",")).(L.map toCsvText)) result
                      in yield tx
                      >> let !progress = "   Progress : " ++ show (100 * (fromIntegral num) / maxRowNum) ++ " % \r"
                      in when (rem num 10 == 0 ) (liftIO (putStr progress >> hFlush stdout ))
                      >> ioCensusRow2Text maxRowNum (num + 1)

{-# INLINE unlinesTL #-}
unlinesTL :: (Monad m) => ConduitT Text Text m ()
unlinesTL =  CC.concatMap (:[T.singleton '\n'])

-- | Converted ファイルに含まれる事業所番号をすべて抽出する（重複なし）
collectAllEstIdx :: [FilePath] -> IO [Text]
collectAllEstIdx files  = print "correcting indeces..."
                        >> runEval . mergenub . concat <$> parMapM getEsIdx files
    where
    getEsIdx :: FilePath -> IO [Text]
    getEsIdx path   =   openFile path ReadMode            >>= \ !h
                    ->  T.lines <$> TO.hGetContents h     >>= \ !cs
                    ->  let !headers =  Map.fromList
                                     $! (flip L.zip) [0 ..]
                                     $! L.map parseHeader
                                     $! L.head
                                     $! parseCSVErr
                                     $! L.head cs
                    in  return  $! runEval
                                $! parMap (getTextErr.(readDataWithMap H事業所番号 headers).head.parseCSVErr)
                                $! tail cs

    getTextErr :: Val -> Text
    getTextErr v = case v of
                 VText tx -> tx
                 _        -> error $ "it is not VText. :" ++ ushow v


------------------------------------------------------------------
-- *  Elements
------------------------------------------------------------------

-- | センサス個票の調査項目（データのヘッダー）
-- * これでデータを抽出する

data Header = H直轄企業コード              -- ^ 型 : VText              概要: 直轄企業コード, 名寄せに用いる
            | H事業所番号                  -- ^ 型 : VText              概要: 事業所番号,事業所の識別に用いる
            | H調査票の種類                -- ^ 型 :                    概要: 調査票の種類
            | H総売上                      -- ^ 型 : Double             概要: ［集計用］売上（収入）金額
            | H地域コード                  -- ^ 型 : Text               概要: [確定]市区町村コード(所在地)
            | H経営組織                    -- ^ 型 :                    概要: 経営組織
            | H管理補助的業務              -- ^ 型 :                    概要: 管理補助的業務
            | H雇用情報                    -- ^ 型 :                    概要: 雇用情報
            | H単独本所支所区分            -- ^ 型 :                    概要: ［事］単独・本所・支所３区分
            | H費用等の内訳                -- ^ 型 : Cars               概要: 費用等の内訳
            | H生産_鉱業_数量              -- ^ 型 : Cars               概要: 生産数量（鉱業）
            | H生産_鉱業_金額              -- ^ 型 : Cars               概要: 生産金額（鉱業）
            | H生産_農林漁業_金額          -- ^ 型 : Cars               概要: 生産金額（農林水産業）
            | H商品別卸売額                -- ^ 型 : Cars               概要: 商品卸売額
            | H商品別小売額                -- ^ 型 : Cars               概要: 年間商品小売額
            | H事業収入_医療福祉           -- ^ 型 :                    概要: 医療福祉の事業収入
            | H事業所形態_医療福祉         -- ^ 型 :                    概要: 事業所の形態（医療福祉）
            | H出荷額_製造業               -- ^ 型 : Cars               概要: 製造品出荷額
            | H在庫額_製造業               -- ^ 型 : Cars               概要: 製造品在庫額
            | H収入額_加工賃               -- ^ 型 : Cars               概要: 加工賃収入額
            | H収入額_製造業以外           -- ^ 型 : Cars               概要: 製造業以外の収入金額
            | H原材料使用額                -- ^ 型 : VDouble               概要: 原材料,燃料,電力の使用額,受託生産費,製造等に関連する外注費
            | H収入内訳_学校               -- ^ 型 : Cars               概要: 学校種類別収入内訳
            | H学校等の種類                -- ^ 型 : VText              概要: 事業所調査票における学校糖の種類
            | H年初製造品在庫額            -- ^ 型 : Double
            | H年末製造品在庫額            -- ^ 型 : Double
            | H年初半製品及び仕掛品        -- ^ 型 : Double
            | H年末半製品及び仕掛品        -- ^ 型 : Double
            | H事業収入_サB                -- ^ 型 : Cars
            | H商品別リース契約高          -- ^ 型 : Cars               概要: リース年間契約高
            | H商品別レンタル売上高        -- ^ 型 : Cars               概要: レンタル年間売上高
            | Hレンタル総売上高            -- ^ 型 : Double             概要: レンタル年間総売上高
            | Hリース年間契約高            -- ^ 型 : Double             概要: リース年間総契約高
            | H相手先別収入割合_サB        -- ^ 型 : E相手先別収入割合  概要: サービス関連産業Bの相手先別収入割合
            | H同業者割合_サB              -- ^ 型 : VDouble
            | H相手先別収入割合_医療福祉   -- ^ 型 : E相手先別収入割合  概要: 医療福祉の相手先別収入割合
            | H修理手数料収入_商業         -- ^ 型 : Cars               概要: 商品販売に関するその他の収入額 内 修理手数料収入
            | H仲立手数料収入_商業         -- ^ 型 : Double             概要: 商品販売に関するその他の収入額 内 仲立手数料収入
            | H商品売上原価                -- ^ 型 : VDouble            概要: 商品売上原価
            | H年初商品手持額              -- ^ 型 : VDouble            概要: 年初商品手持額
            | H年末商品手持額              -- ^ 型 : VDouble            概要: 年末商品手持額
            | H年間仕入額                  -- ^ 型 : VDouble            概要: 年間所品仕入額
            | H対象年度                    -- ^ 型 : Int                概要: 調査年度
            | H消費税記入の別              -- ^ 型 : Bool               概要: 消費税込記入の別
            | H事業別売上高                -- ^ 型 : Cars               概要: 事業別売上高
            | H輸出割合                    -- ^ 型 : Double             概要: 製造品出荷額等に占める直接輸出額の割合
            | H事業形態                    -- ^ 型 : BusinessStyle      概要: 事業の形態
            | H事前格付_事業所             -- ^ 型 : E産業格付          概要: デフォルトの産業格付け
            | H事前格付_企業               -- ^ 型 : E産業格付          概要: デフォルトの産業格付け
            | H主な事業の種類              -- ^ 型 : VText              概要: サA事業所調査票の事業選択
            | H産業格付                    -- ^ 型 : E産業格付
            | H信用共済事業の有無          -- ^ 型 : Bool               概要: 信用・共済事業の有無
            | H協同組合の種類              -- ^ 型 :                    概要:
            | H団体の種類                  -- ^ 型 : E団体の種類
            | H8時間換算雇用者数_サB       -- ^ 型 : Double
            | H8時間換算雇用者数_商業      -- ^ 型 : Double
            | H売場面積                    -- ^ 型 : Double
            | Hセルフサービス              -- ^ 型 : Bool
            | H開店閉店期間                -- ^ 型 : Int
            | H販売形態                    -- ^ 型 : E販売形態
            | H商品形態                    -- ^ 型 : E商品形態
            | H店舗形態_商業               -- ^ 型 : E店舗形態
            | H店舗形態_サB                -- ^ 型 : VText
            | H事業収入_建サA              -- ^ 型 : Cars               概要: 事業収入1ー10位
            | H工事種類                    -- ^ 型 : E工事種類          概要: 業態別工事種類
            | H金融業保険業の事業種類      -- ^ 型 : VInt               概要: 1 - 19 のInt
            | H事業所別生産物別売上高      -- ^ 型 : Cars               概要:
            | H年初原材料及び燃料          -- ^ 型 : Double             使用しない
            | H年末原材料及び燃料          -- ^ 型 : Double             使用しない
            | H商品販売額最多部門          -- ^ 型 :                    使用しない 概要: 年間商品販売額が多い部門
            deriving (Eq, Enum, Ord, Ix, Show, Read)

parserHeader  =  f H直轄企業コード
             <|> f H事業所番号
             <|> f H調査票の種類
             <|> f H総売上
             <|> f H地域コード
             <|> f H経営組織
             <|> f H管理補助的業務
             <|> f H雇用情報
             <|> f H単独本所支所区分
             <|> f H費用等の内訳
             <|> f H生産_鉱業_数量
             <|> f H生産_鉱業_金額
             <|> f H生産_農林漁業_金額
             <|> f H商品別卸売額
             <|> f H商品別小売額
             <|> f H事業収入_医療福祉
             <|> f H事業所形態_医療福祉
             <|> f H出荷額_製造業
             <|> f H在庫額_製造業
             <|> f H収入額_加工賃
             <|> f H収入額_製造業以外
             <|> f H原材料使用額
             <|> f H収入内訳_学校
             <|> f H学校等の種類
             <|> f H年初製造品在庫額
             <|> f H年末製造品在庫額
             <|> f H年初半製品及び仕掛品
             <|> f H年末半製品及び仕掛品
             <|> f H事業収入_サB
             <|> f H商品別リース契約高
             <|> f H商品別レンタル売上高
             <|> f Hレンタル総売上高
             <|> f Hリース年間契約高
             <|> f H相手先別収入割合_サB
             <|> f H同業者割合_サB
             <|> f H相手先別収入割合_医療福祉
             <|> f H修理手数料収入_商業
             <|> f H仲立手数料収入_商業
             <|> f H商品売上原価
             <|> f H年初商品手持額
             <|> f H年末商品手持額
             <|> f H年間仕入額
             <|> f H対象年度
             <|> f H消費税記入の別
             <|> f H事業別売上高
             <|> f H輸出割合
             <|> f H事業形態
             <|> f H事前格付_事業所
             <|> f H事前格付_企業
             <|> f H主な事業の種類
             <|> f H産業格付
             <|> f H信用共済事業の有無
             <|> f H協同組合の種類
             <|> f H団体の種類
             <|> f H8時間換算雇用者数_サB
             <|> f H8時間換算雇用者数_商業
             <|> f H売場面積
             <|> f Hセルフサービス
             <|> f H開店閉店期間
             <|> f H販売形態
             <|> f H商品形態
             <|> f H店舗形態_商業
             <|> f H店舗形態_サB
             <|> f H事業収入_建サA
             <|> f H工事種類
             <|> f H金融業保険業の事業種類
             <|> f H事業所別生産物別売上高
             <|> f H年初原材料及び燃料
             <|> f H年末原材料及び燃料
             <|> f H商品販売額最多部門
            where f s = try( string (T.pack (ushow s))) >> return s


headerList = [H直轄企業コード ..  H事業所別生産物別売上高]

outputHeader = T.concat $ (L.intersperse (T.pack ",")) $ L.map (T.pack . ushow) headerList


{- | Read が遅すぎるのでHeaderの読み込みはこちらのパーサーを用いる．

Exhausive pattern Errorが出る場合 Win (\r\n) <-> Unix 系
での改行コードのエラーでCSVのパースができてない可能性が高い.-}

parseHeader :: Text -> Header
parseHeader tx = case parse parserHeader tx of
        Done a r        -> r
        Fail a xs err   -> error $ "Can not parse Header :" ++ ushow err
                                                            ++ ushow xs
                                                            ++ ushow a

---------------------------------------------------------
-- ** Val型
---------------------------------------------------------

{- | 変換される値は全てVal型に統一

 * E型のデータ型をV型でラップ
 * アンダーバーで抽出 -}

data Val
    = Null
    | VInt                  { int                           ::  {-# UNPACK #-} !Int                   }
    | VDouble               { double                        ::  {-# UNPACK #-} !Double                }
    | VText                 { text                          ::  {-# UNPACK #-} !Text                  }
    | VBool                 { bool                          ::  {-# UNPACK #-} !Bool                  }
    | VCars                 { cars                          ::                 !Cars                  }
    | V調査票の種類         { _調査票の種類                 ::  {-# UNPACK #-} !E調査票の種類         }
    | V管理補助的業務       { _管理補助的業務               ::  {-# UNPACK #-} !E管理補助的業務       }
    | V雇用情報             { _雇用情報                     ::  {-# UNPACK #-} !E雇用情報             }
    | V産業格付             { _産業格付                     ::  {-# UNPACK #-} !E産業格付             }
    | V事業形態             { _事業形態                     ::  {-# UNPACK #-} !E事業形態             }
    | V経営組織             { _経営組織                     ::  {-# UNPACK #-} !E経営組織             }
    | V単独本所支所区分     { _単独本所支所区分             ::  {-# UNPACK #-} !E単独本所支所区分     }
    | V商品販売額最多部門   { _商品販売額最多部門           ::  {-# UNPACK #-} !E商品販売額最多部門   }
    | V事業所形態_医療福祉  { _事業所形態_医療福祉          ::  {-# UNPACK #-} !E事業所形態_医療福祉  }
    | V事業収入_医療福祉    { _事業収入_医療福祉            ::  {-# UNPACK #-} !E事業収入_医療福祉    }
    | V団体の種類           { _団体の種類                   ::  {-# UNPACK #-} !E団体の種類           }
    | V協同組合の種類       { _協同組合の種類               ::  {-# UNPACK #-} !E協同組合の種類       }
    | V相手先別収入割合     { _相手先別収入割合             ::  {-# UNPACK #-} !E相手先別収入割合     }
    | V店舗形態_商業        { _店舗形態_商業                ::  {-# UNPACK #-} !E店舗形態_商業        }
    | V販売形態             { _販売形態                     ::  {-# UNPACK #-} !E販売形態             }
    | V商品形態             { _商品形態                     ::  {-# UNPACK #-} !E商品形態             }
    | V工事種類             { _工事種類                     ::  {-# UNPACK #-} !E工事種類             }
    deriving (Read, Eq, Generic)

instance NFData Val

instance Show Val where
    show Null                      = "Null"
    show (VInt                 x)  = "VInt {int = "                                    ++ show  x ++ "}"
    show (VDouble              x)  = "VDouble {double = "                              ++ show  x ++ "}"
    show (VText                x)  = "VText {text = "                                  ++ ushow x ++ "}"
    show (VBool                x)  = "VBool {bool = "                                  ++ show  x ++ "}"
    show (VCars                x)  = "VCars {cars = "                                  ++ show  x ++ "}"
    show (V調査票の種類        x)  = "V調査票の種類 {_調査票の種類 = "                 ++ show  x ++ "}"
    show (V管理補助的業務      x)  = "V管理補助的業務 {_管理補助的業務 = "             ++ show  x ++ "}"
    show (V雇用情報            x)  = "V雇用情報 {_雇用情報 = "                         ++ show  x ++ "}"
    show (V産業格付            x)  = "V産業格付 {_産業格付 = "                         ++ show  x ++ "}"
    show (V事業形態            x)  = "V事業形態 {_事業形態 = "                         ++ show  x ++ "}"
    show (V経営組織            x)  = "V経営組織 {_経営組織 = "                         ++ show  x ++ "}"
    show (V単独本所支所区分    x)  = "V単独本所支所区分 {_単独本所支所区分 = "         ++ show  x ++ "}"
    show (V商品販売額最多部門  x)  = "V商品販売額最多部門 {_商品販売額最多部門 = "     ++ show  x ++ "}"
    show (V事業所形態_医療福祉 x)  = "V事業所形態_医療福祉 {_事業所形態_医療福祉 = "   ++ show  x ++ "}"
    show (V事業収入_医療福祉   x)  = "V事業収入_医療福祉 {_事業収入_医療福祉 = "       ++ show  x ++ "}"
    show (V団体の種類          x)  = "V団体の種類 {_団体の種類 = "                     ++ show  x ++ "}"
    show (V協同組合の種類      x)  = "V協同組合の種類 {_協同組合の種類 = "             ++ show  x ++ "}"
    show (V相手先別収入割合    x)  = "V相手先別収入割合 {_相手先別収入割合 = "         ++ show  x ++ "}"
    show (V店舗形態_商業       x)  = "V店舗形態_商業 {_店舗形態_商業 = "               ++ show  x ++ "}"
    show (V販売形態            x)  = "V販売形態 {_販売形態 = "                         ++ show  x ++ "}"
    show (V商品形態            x)  = "V商品形態 {_商品形態 = "                         ++ show  x ++ "}"
    show (V工事種類            x)  = "V工事種類 {_工事種類 = "                         ++ show  x ++ "}"

{-# INLINE parserNull #-}
parserNull :: Parser Val
parserNull    =  string (T.pack "Null") >> return Null

{-# INLINE parserVInt#-}
parserVInt :: Parser ValInt
parserVInt    =  string (T.pack "VInt {int = ")
             >> DAT.double >>= \fl
             -> char '}'
             >> return (VInt (truncate fl))

{-# INLINE parserVDouble #-}
parserVDouble :: Parser ValDouble
parserVDouble = string (T.pack "VDouble {double = ")
             >> DAT.double >>= \fl
             -> char '}'
             >> return (VDouble fl)

{-# INLINE parserVText #-}
parserVText :: Parser ValText
parserVText  =  string (T.pack "VText {text = ")
             >> quotedCell >>= \tx
             -> char '}'
             >> return  (VText (T.pack tx))

{-# INLINE parserVBool #-}
parserVBool :: Parser ValBool
parserVBool   = string (T.pack "VBool {bool = ")
             >> (try (string (T.pack "True")  >> return (VBool True ))
                <|> (string (T.pack "False") >> return (VBool False))) >>= \bl
             -> char '}'
             >> return bl

{-# INLINE parserVCars #-}
parserVCars :: Parser ValCars
parserVCars   =  string (T.pack "VCars {cars = [")
             >> try (sepBy parseCar (char ',') >>= \cs -> return cs) >>= \ xs
             -> string (T.pack "]}")
             >> return (VCars (V.fromList xs))

-- | Val のコンストラクタごとのパーサーを指定してパースする
{-# INLINE parserVJap #-}
parserVJap :: String -> Parser a -> (a -> Val) -> Parser Val
parserVJap str p vf =   string (T.pack ("V" ++ str ++ " {_" ++ str ++ " = "))
                    >>  p >>= \v ->  char '}' >> return (vf v)



{-# INLINE parserV調査票の種類     #-}
parserV調査票の種類        = parserVJap "調査票の種類"          parserE調査票の種類        V調査票の種類

{-# INLINE parserV管理補助的業務    #-}
parserV管理補助的業務      = parserVJap "管理補助的業務"        parserE管理補助的業務      V管理補助的業務

{-# INLINE parserV雇用情報       #-}
parserV雇用情報            = parserVJap "雇用情報"              parserE雇用情報            V雇用情報

{-# INLINE parserV産業格付       #-}
parserV産業格付            = parserVJap "産業格付"              parserE産業格付            V産業格付

{-# INLINE parserV事業形態       #-}
parserV事業形態            = parserVJap "事業形態"              parserE事業形態            V事業形態

{-# INLINE parserV経営組織       #-}
parserV経営組織            = parserVJap "経営組織"              parserE経営組織            V経営組織

{-# INLINE parserV単独本所支所区分   #-}
parserV単独本所支所区分    = parserVJap "単独本所支所区分"      parserE単独本所支所区分    V単独本所支所区分

{-# INLINE parserV商品販売額最多部門  #-}
parserV商品販売額最多部門  = parserVJap "商品販売額最多部門"    parserE商品販売額最多部門  V商品販売額最多部門

{-# INLINE parserV事業所形態_医療福祉 #-}
parserV事業所形態_医療福祉 = parserVJap "事業所形態_医療福祉"   parserE事業所形態_医療福祉 V事業所形態_医療福祉

{-# INLINE parserV事業収入_医療福祉  #-}
parserV事業収入_医療福祉   = parserVJap "事業収入_医療福祉"     parserE事業収入_医療福祉   V事業収入_医療福祉

{-# INLINE parserV団体の種類      #-}
parserV団体の種類          = parserVJap "団体の種類"            parserE団体の種類          V団体の種類

{-# INLINE parserV協同組合の種類    #-}
parserV協同組合の種類      = parserVJap "協同組合の種類"        parserE協同組合の種類      V協同組合の種類

{-# INLINE parserV相手先別収入割合   #-}
parserV相手先別収入割合    = parserVJap "相手先別収入割合"      parserE相手先別収入割合    V相手先別収入割合

{-# INLINE parserV店舗形態_商業    #-}
parserV店舗形態_商業       = parserVJap "店舗形態_商業"         parserE店舗形態_商業       V店舗形態_商業

{-# INLINE parserV販売形態       #-}
parserV販売形態            = parserVJap "販売形態"              parserE販売形態            V販売形態

{-# INLINE parserV商品形態       #-}
parserV商品形態            = parserVJap "商品形態"              parserE商品形態            V商品形態

{-# INLINE parserV工事種類       #-}
parserV工事種類            = parserVJap "工事種類"              parserE工事種類            V工事種類

-- | Read が遅すぎるのでValの読み込みはこちらのパーサーを用いる．
{-# INLINE parserVal #-}
parserVal    =  try parserNull
            <|> try parserVInt
            <|> try parserVDouble
            <|> try parserVText
            <|> try parserVBool
            <|> try parserVCars
            <|> try parserV調査票の種類
            <|> try parserV管理補助的業務
            <|> try parserV雇用情報
            <|> try parserV産業格付
            <|> try parserV事業形態
            <|> try parserV経営組織
            <|> try parserV単独本所支所区分
            <|> try parserV商品販売額最多部門
            <|> try parserV事業所形態_医療福祉
            <|> try parserV事業収入_医療福祉
            <|> try parserV団体の種類
            <|> try parserV協同組合の種類
            <|> try parserV相手先別収入割合
            <|> try parserV店舗形態_商業
            <|> try parserV販売形態
            <|> try parserV商品形態
            <|> try parserV工事種類

{- | Read が遅すぎるのでValの読み込みはこちらのパーサーを用いる．

Exhausive pattern Errorが出る場合 Win (\r\n) <-> Unix 系
での改行コードのエラーでCSVのパースができてない可能性が高い -}

{-# INLINE parseVal #-}
parseVal :: Text -> Val
parseVal tx = case DAT.parse parserVal tx of
        Done a r        -> r
        Fail a xs err   -> error $ "Error on parseVal : " ++ show err
                                                          ++ show xs
                                                          ++ show a


------------------------------------------------------------------
-- ** Val型タイプシノニム
------------------------------------------------------------------

-- Valだけだとわかりにくいので,タイプシノニムを作る


-- *** Int
------------------------------------------------------------------
type ValInt                       = Val
type Val開店閉店期間              = Val

-- *** Double
------------------------------------------------------------------
type ValDouble                    = Val
type Valリース年間契約高          = Val
type Valレンタル総売上高          = Val
type Val原材料使用額              = Val
type Val売場面積                  = Val
type Val修理手数料収入_商業       = Val
type Val仲立手数料収入_商業       = Val
type Val輸出割合                  = Val
type Val同業者割合_サB            = Val
type Val総売上                    = Val
type Val年末製造品在庫額          = Val
type Val年初製造品在庫額          = Val


-- *** Text
------------------------------------------------------------------
type ValText                      = Val
type Val学校等の種類              = Val
type Val金融業保険業の事業種類    = Val
type Val主な事業の種類            = Val
type Val店舗形態_サB              = Val
type Val直轄企業コード            = Val
type Val地域コード                = Val


-- | NullかVTextかという状況で使用する
--
-- No match in record selector text

textWithNull (VText x) = x
textWithNull Null      = T.pack "Null"


-- *** Bool
------------------------------------------------------------------
type ValBool                      = Val
type Val信用共済事業の有無        = Val
type Valセルフサービス            = Val

-- *** Cars
------------------------------------------------------------------
type ValCars                      = Val
type Val事業別売上高              = Val
type Val事業所別生産物別売上高    = Val
type Val生産_鉱業_数量            = Val
type Val生産_鉱業_金額            = Val
type Val生産_農林漁業_金額        = Val
type Val収入内訳_学校             = Val
type Val費用等の内訳              = Val
type Val収入額_製造業以外         = Val
type Val収入額_加工賃             = Val
type Val出荷額_製造業             = Val
type Val商品別卸売額              = Val
type Val商品別小売額              = Val
type Val事業収入_建サA            = Val
type Val事業収入_サB              = Val
type Val商品別レンタル売上高      = Val
type Val商品別リース契約高        = Val
type Val在庫額_製造業             = Val

type Cars事業別売上高             = Cars
type Cars事業所別生産物別売上高   = Cars
type Cars生産_鉱業_数量           = Cars
type Cars生産_鉱業_金額           = Cars
type Cars生産_農林漁業_金額       = Cars
type Cars収入内訳学校_学校        = Cars
type Cars費用等の内訳             = Cars
type Cars収入額_製造業以外        = Cars
type Cars収入額_加工賃            = Cars
type Cars出荷額_製造業            = Cars
type Cars商品別卸売額             = Cars
type Cars商品別小売額             = Cars
type Cars事業収入_建サA           = Cars
type Cars事業収入_サB             = Cars
type Cars商品別レンタル売上高     = Cars
type Cars商品別リース契約高       = Cars
type Cars在庫額_製造業            = Cars


-- *** 産業格付け
------------------------------------------------------------------
type Val産業格付                  = Val
type Val事前格付_企業             = Val
type Val事前格付_事業所           = Val

-- *** その他独自型
------------------------------------------------------------------
type Val調査票の種類              = Val
type Val管理補助的業務            = Val
type Val雇用情報                  = Val
type Val事業形態                  = Val
type Val経営組織                  = Val
type Val単独本所支所区分          = Val
type Val商品販売額最多部門        = Val
type Val事業所形態_医療福祉       = Val
type Val事業収入_医療福祉         = Val
type Val団体の種類                = Val
type Val協同組合の種類            = Val
type Val店舗形態_商業             = Val
type Val販売形態                  = Val
type Val商品形態                  = Val
type Val工事種類                  = Val
type Val相手先別収入割合          = Val
type Val相手先別収入割合_サB      = Val
type Val相手先別収入割合_医療福祉 = Val




---------------------------------------------------------
-- * データ型の設計
-----------------------------------------------------------
-- ** 直轄企業コード
-----------------------------------------------------------
{- |
     経済センサスの調査票には，平成24，28年共に，「市区町村コード，調査区番号，事業所番号，＊コード」が記載されており，
     同一企業に属する支所等は全て同一のコードを持つ．

     この事業所コードとは別に，企業内において連番される2桁の整理番号が存在し，
     これらのコードを全て併せて「直轄企業コード」と呼ぶ．
     直轄企業コードは全事業所にそれぞれ固有であり，且つ，各事業所がどの企業に属するのかを判別することを可能にする．
-}

type E直轄企業コード = Text


------------------------------------------------------------------
-- ** 雇用情報
------------------------------------------------------------------

{- |   企業調査票においては,企業雇用者数, 企業個人事業者数, 企業事業従業者数が,
事業所調査票においては, 事業所雇用者数, 事業所雇用者数, 事業所事業従業者数が推計において利用される.
-}

data E雇用情報      = E雇用情報
                    { _企雇用者数                      :: {-# UNPACK #-} !Int
                    , _企個人事業主                    :: {-# UNPACK #-} !Int
                    , _企事業従業者数                  :: {-# UNPACK #-} !Int
                    , _事雇用者数                      :: {-# UNPACK #-} !Int
                    , _事個人事業主                    :: {-# UNPACK #-} !Int
                    , _事事業従業者数                  :: {-# UNPACK #-} !Int }
                    deriving (Eq, Show,Read, Generic)
instance NFData E雇用情報

parserE雇用情報 =  do
                string (T.pack "E雇用情報 {")
                d1 <- f "_企雇用者数 = "
                d2 <- f "_企個人事業主 = "
                d3 <- f "_企事業従業者数 = "
                d4 <- f "_事雇用者数 = "
                d5 <- f "_事個人事業主 = "
                d6 <- f "_事事業従業者数 = "
                return (E雇用情報 d1 d2 d3 d4 d5 d6)

            where
            f :: String -> Parser Int
            f s =   do
                    string (T.pack s)
                    di <-  many digit
                    try (string (T.pack ", ")) <|> (string (T.pack "}"))
                    return (fastReadInt di)


------------------------------------------------------------------
-- ** 事業の業態 個人経営調査票のみ（？）
------------------------------------------------------------------

data E事業形態  = E製造卸売       -- ^ 主に製造して出荷又は卸売
                | E製造遠隔小売   -- ^ 主に製造して通信販売・ネット販売等で小売
                | E加工           -- ^ 主に他の業者から支給された原材料により製造・加工
                | E自企業卸売     -- ^ 主に同一企業の他の事業所で製造・加工した物品を卸売
                | E他企業卸売     -- ^ 主に他企業の事業所（下請先も含む）で生産・加工した物品を卸売
                | E製造小売       -- ^ 主に製造してその場所で小売
                | E店頭小売       -- ^ 主に他の事業所から仕入れた商品を店舗で小売
                | E遠隔小売       -- ^ 主に仕入れた商品を店舗を持たずに通信販売・ネット販売・訪問販売等で小売
                | E食品小売       -- ^ 主に調理済みの料理品を小売
                | E料理配達       -- ^ 主に顧客の注文で調理する料理品を提供（配達を含む）
                | E土木           -- ^ 土木工事の施工額が、施工額全体の80％以上
                | E建築           -- ^ 建築工事の施工額が、施工額全体の80％以上
                | E工事           -- ^ 土木工事と建築工事の施工額がいずれも施工額全体の80％未満
                deriving (Eq, Enum, Show, Read, Generic)
instance NFData E事業形態


parserE事業形態 =    f E製造卸売
                <|>  f E製造遠隔小売
                <|>  f E加工
                <|>  f E自企業卸売
                <|>  f E他企業卸売
                <|>  f E製造小売
                <|>  f E店頭小売
                <|>  f E遠隔小売
                <|>  f E食品小売
                <|>  f E料理配達
                <|>  f E土木
                <|>  f E建築
                <|>  f E工事
                where f s = try( string (T.pack (ushow s))) >> return s


------------------------------------------------------------------
-- ** 管理補助的業務
------------------------------------------------------------------
{- |  事業所調査票における調査項目「管理・補助的業務」では，
事業所が管理補助的業務を行っている場合には，「管理運営業務，補助的業務，自家用倉庫」から選択する形式の調査を行っている．
経済センサス分類においては，特殊な項目として，
「主として管理事務を行う本社等」，「その他の管理，補助的経済活動を行う事業所」，「自家用倉庫」が存在し，
これらの項目への産業格付けにおいて利用される．-}


data E管理補助的業務    = E管理補助的業務
                        | E補助的業務
                        | E自家用倉庫
                        deriving (Eq, Enum, Show, Read, Generic)
instance NFData E管理補助的業務

parserE管理補助的業務 =  try( string (T.pack "E管理補助的業務")  >> return E管理補助的業務 )
                    <|>  try( string (T.pack "E補助的業務")      >> return E補助的業務     )
                    <|>  try( string (T.pack "E自家用倉庫")      >> return E自家用倉庫     )

------------------------------------------------------------------
-- ** 経営組織
------------------------------------------------------------------

data E経営組織      = E個人経営
                    | E株式会社
                    | E合名会社
                    | E合同会社
                    | E会社以外の法人
                    | E外国の会社
                    | E法人でない団体
                    deriving (Eq,Enum,Show, Read, Generic)
instance NFData E経営組織

parserE経営組織 =    f E個人経営
                <|>  f E株式会社
                <|>  f E合名会社
                <|>  f E合同会社
                <|>  f E会社以外の法人
                <|>  f E外国の会社
                <|>  f E法人でない団体
                where f s = try( string (T.pack (ushow s))) >> return s

-- ----------------------------------------------------------------
-- ** 単独事業所・本所・支所の別等
-- ----------------------------------------------------------------

data E単独本所支所区分      = E単独事業所
                            | E本所
                            | E支所
                            deriving (Eq,Enum,Read,Show, Generic)
instance NFData E単独本所支所区分

parserE単独本所支所区分  =   try( string (T.pack "E単独事業所")     >> return E単独事業所         )
                        <|>  try( string (T.pack "E本所")           >> return E本所         )
                        <|>  try( string (T.pack "E支所")           >> return E支所         )

------------------------------------------------------
-- ** 産業格付け
------------------------------------------------------
type Goods_name = Text
type Goods_code = Text

{- |  事業所/企業に格付けられた産業を表す．調査票上に項目はなく，
他の情報から「4.1.1.5章 産業格付け」において説明される産業格付け処理を経て決定されるパラメーター
-}

data E産業格付 = E産業格付  { _大分類       :: {-# UNPACK #-} !Goods_code
                            , _15分類       :: {-# UNPACK #-} !Goods_code
                            , _中分類       :: {-# UNPACK #-} !Goods_code
                            , _小分類       :: {-# UNPACK #-} !Goods_code
                            , _35分類       :: {-# UNPACK #-} !Goods_code
                            , _細分類       :: {-# UNPACK #-} !Goods_code
                            } deriving (Eq, Read, Generic)
instance NFData E産業格付

instance Show E産業格付 where
    show (E産業格付 x1 x2 x3 x4 x5 x6) =   "E産業格付 {_大分類 = "   ++ ushow x1
                                       ++           ", _15分類 = "   ++ ushow x2
                                       ++           ", _中分類 = "   ++ ushow x3
                                       ++           ", _小分類 = "   ++ ushow x4
                                       ++           ", _35分類 = "   ++ ushow x5
                                       ++           ", _細分類 = "   ++ ushow x6
                                       ++           "}"




parserE産業格付 =  do
                string (T.pack "E産業格付 {")
                d1 <- f "_大分類 = "
                d2 <- f "_15分類 = "
                d3 <- f "_中分類 = "
                d4 <- f "_小分類 = "
                d5 <- f "_35分類 = "
                d6 <- f "_細分類 = "
                return (E産業格付 d1 d2 d3 d4 d5 d6)

            where
            f :: String -> Parser Text
            f s =   do
                    string (T.pack s)
                    di <-  quotedCell
                    try (string (T.pack ", ")) <|> (string (T.pack "}"))
                    return (T.pack di)


------------------------------------------------------------------
-- ** 調査票の種別
------------------------------------------------------------------
data E調査票    = E単独事業所調査票
                | E産業共通調査票
                | E企業調査票
                | E事業所調査票
                | E団体調査票
                | E個人経営調査票
                deriving (Eq, Enum, Read, Show, Generic)
instance NFData E調査票


parserE調査票    =   f E単独事業所調査票
                <|>  f E産業共通調査票
                <|>  f E企業調査票
                <|>  f E事業所調査票
                <|>  f E団体調査票
                <|>  f E個人経営調査票
                where f s = try( string (T.pack (ushow s))) >> return s

data E対象産業   = E産業なし            | E農林漁業         | E鉱業
                 | E製造業              | E商業             | E医療福祉
                 | E学校教育            | E協同組合         | EサービスB
                 | E共通                | E建設サービスA    | E団体
                 | E建設サービスA学校   | E全産業
                 deriving (Eq, Enum, Read,Show, Generic)
instance NFData E対象産業

parserE対象産業  =   f E産業なし
                <|>  f E農林漁業
                <|>  f E鉱業
                <|>  f E製造業
                <|>  f E商業
                <|>  f E医療福祉
                <|>  f E学校教育
                <|>  f E協同組合
                <|>  f EサービスB
                <|>  f E共通
                <|>  f E建設サービスA
                <|>  f E団体
                <|>  f E建設サービスA学校
                <|>  f E全産業
                where f s = try( string (T.pack (ushow s))) >> return s

data E回答主体  = E個人経営者用
                | E団体法人用
                | E指定なし
                deriving (Eq, Enum, Read,Show, Generic)
instance NFData E回答主体

parserE回答主体  =   try( string (T.pack "E個人経営者用")   >> return E個人経営者用 )
                <|>  try( string (T.pack "E団体法人用")     >> return E団体法人用   )
                <|>  try( string (T.pack "E指定なし")       >> return E指定なし     )

data E調査票の種類 = E調査票の種類  { _調査票   :: {-# UNPACK #-} !E調査票
                                    , _対象産業 :: {-# UNPACK #-} !E対象産業
                                    , _回答主体 :: {-# UNPACK #-} !E回答主体}
                                    deriving (Eq,Read,Show, Generic)

instance NFData E調査票の種類


-- | >>> parseTest parserE調査票の種類 $ T.pack $ ushow $ E調査票の種類 E単独事業所調査票 E団体 E指定なし
--   >>> Done "" (E調査票の種類 {_調査票 = E単独事業所調査票, _対象産業 = E団体, _回答主体 = E指定なし})

parserE調査票の種類 =  do
                string (T.pack "E調査票の種類 {")

                string (T.pack "_調査票 = ")
                d1 <- parserE調査票
                string (T.pack ", ")

                string (T.pack "_対象産業 = ")
                d2 <- parserE対象産業
                string (T.pack ", ")

                string (T.pack "_回答主体 = ")
                d3 <- parserE回答主体
                string (T.pack "}")
                return (E調査票の種類 d1 d2 d3)

------------------------------------------------------------------
-- ** 年間商品販売額等
------------------------------------------------------------------
-- | 年間商品販売額が多い部門
data E商品販売額最多部門 = E小売 | E卸売  deriving (Eq,Show, Read, Generic)
instance NFData E商品販売額最多部門

parserE商品販売額最多部門    =  f E小売
                            <|> f E卸売
                            where f s = try( string (T.pack (ushow s))) >> return s

------------------------------------------------------------------
-- ** 医療，福祉の事業収入内訳
------------------------------------------------------------------
-- | 医療事業形態における7区分
data E事業収入_医療福祉     = E事業収入_医療福祉
                              { _保険診療収入         :: {-# UNPACK #-} !Double
                              , _保険外診療収入       :: {-# UNPACK #-} !Double
                              , _施設介護収入         :: {-# UNPACK #-} !Double
                              , _通所介護訪問介護収入 :: {-# UNPACK #-} !Double
                              , _社会保険事業収入     :: {-# UNPACK #-} !Double
                              , _保健衛生事業収入     :: {-# UNPACK #-} !Double
                              , _社会福祉事業収入     :: {-# UNPACK #-} !Double }
                              deriving (Show, Read, Eq, Generic)

instance NFData E事業収入_医療福祉

parserE事業収入_医療福祉 =  do
                string (T.pack "E事業収入_医療福祉 {")
                d1 <- f "_保険診療収入 = "
                d2 <- f "_保険外診療収入 = "
                d3 <- f "_施設介護収入 = "
                d4 <- f "_通所介護訪問介護収入 = "
                d5 <- f "_社会保険事業収入 = "
                d6 <- f "_保健衛生事業収入 = "
                d7 <- f "_社会福祉事業収入 = "
                return (E事業収入_医療福祉 d1 d2 d3 d4 d5 d6 d7)
            where
            f :: String -> Parser Double
            f s =   do
                    string (T.pack s)
                    di <-  DAT.double
                    try (string (T.pack ", ")) <|> (string (T.pack "}"))
                    return di


------------------------------------------------------------------
-- ** 事業所の形態，主な事業の内容（医療，福祉）
------------------------------------------------------------------

-- | 医療事業形態における32区分
data E事業所形態_医療福祉
        = E一般病院                   | E精神科病院                        | E有床診療所
        | E無床診療所                 | E歯科診療所                        | E助産所助産師業
        | E看護業                     | E施術業                            | Eその他の療養所
        | E歯科技工所                 | Eその他の医療に附帯するサービス業  | E結核健康相談施設
        | E精神保健相談施設           | E母子健康相談施設                  | Eその他の健康相談施設
        | E検査業                     | E消毒業                            | Eその他の保健衛生
        | E社会保険事業団体           | E保育所                            | Eその他の児童福祉事業
        | E特別養護老人ホーム         | E介護老人保健施設                  | E通所短期入所介護事業
        | E訪問介護事業               | E認知症老人グループホーム          | E有料老人ホーム
        | Eその他の老人福祉介護事業   | E居住支援事業                      | Eその他の障碍者福祉事業
        | E更生保護事業               | Eその他の社会保険社会福祉介護事業
        deriving (Show,Enum, Eq, Read, Ord, Generic)

instance NFData E事業所形態_医療福祉

parserE事業所形態_医療福祉   =  f E一般病院
                            <|> f E無床診療所
                            <|> f E看護業
                            <|> f E歯科技工所
                            <|> f E精神保健相談施設
                            <|> f E検査業
                            <|> f E社会保険事業団体
                            <|> f E特別養護老人ホーム
                            <|> f E訪問介護事業
                            <|> f Eその他の老人福祉介護事業
                            <|> f E更生保護事業
                            <|> f E精神科病院
                            <|> f E歯科診療所
                            <|> f E施術業
                            <|> f Eその他の医療に附帯するサービス業
                            <|> f E母子健康相談施設
                            <|> f E消毒業
                            <|> f E保育所
                            <|> f E介護老人保健施設
                            <|> f E認知症老人グループホーム
                            <|> f E居住支援事業
                            <|> f Eその他の社会保険社会福祉介護事業
                            <|> f E有床診療所
                            <|> f E助産所助産師業
                            <|> f Eその他の療養所
                            <|> f E結核健康相談施設
                            <|> f Eその他の健康相談施設
                            <|> f Eその他の保健衛生
                            <|> f Eその他の児童福祉事業
                            <|> f E通所短期入所介護事業
                            <|> f E有料老人ホーム
                            <|> f Eその他の障碍者福祉事業
                            where f s = try( string (T.pack (ushow s))) >> return s

parseE事業所形態_医療福祉 :: Text ->  E事業所形態_医療福祉
parseE事業所形態_医療福祉 tx = case parse parserE事業所形態_医療福祉 tx of
        Done a r        -> r
        Fail a xs err   -> error $ "Can not parse E事業所形態_医療福祉 :"   ++ ushow a
                                                                            ++ ushow xs
                                                                            ++ ushow err


------------------------------------------------------------------
-- ** 団体の種類
------------------------------------------------------------------

data E団体の種類     =  E政治団体
                      | E経済団体
                      | E労働団体
                      | E学術団体文化団体
                      | Eその他の団体
                      | E神道系宗教
                      | E仏教系宗教
                      | Eキリスト教系宗教
                      | Eその他の宗教
                    deriving (Show, Read, Eq, Ord, Generic)
instance NFData E団体の種類


parserE団体の種類    =  f E政治団体
                    <|> f E経済団体
                    <|> f E労働団体
                    <|> f E学術団体文化団体
                    <|> f Eその他の団体
                    <|> f E神道系宗教
                    <|> f E仏教系宗教
                    <|> f Eキリスト教系宗教
                    <|> f Eその他の宗教
                    where f s = try( string (T.pack (ushow s))) >> return s


parseE団体の種類 :: Text ->  E団体の種類
parseE団体の種類 tx = case parse parserE団体の種類 tx of
        Done a r        -> r
        Fail a xs err   -> error $ "Can not parse E団体の種類 :"    ++ ushow a   ++ " , "
                                                                    ++ ushow xs
                                                                    ++ ushow err
------------------------------------------------------------------
-- ** 協同組合の種類
------------------------------------------------------------------
data E協同組合の種類   = E農業協同組合
                       | E漁業協同組合
                       | E水産加工協同組合
                       | E森林組合
                       | E事業協同組合            -- ^ 平成28年は,その他の事業協同組合と事業協同組合が統合
                       | E協同組合以外
                       | Eその他の事業協同組合
                       deriving (Show,Read,Eq,Ord,Generic)
instance NFData E協同組合の種類

parserE協同組合の種類     = f E農業協同組合
                        <|> f E漁業協同組合
                        <|> f E水産加工協同組合
                        <|> f E森林組合
                        <|> f E事業協同組合
                        <|> f E協同組合以外
                        <|> f Eその他の事業協同組合
                        where f s = try( string (T.pack (ushow s))) >> return s


parseE協同組合の種類 :: Text ->  E協同組合の種類
parseE協同組合の種類 tx = case parse parserE協同組合の種類 tx of
        Done a r        -> r
        Fail a xs err   -> error $ "Can not parse E協同組合の種類 :"    ++ ushow a
                                                                        ++ ushow xs
                                                                        ++ ushow err

------------------------------------------------------------------
-- ** 医療福祉の相手先別収入割合, サービス関連産業Bの相手先別収入割合
------------------------------------------------------------------

data E相手先別収入割合  = E相手先別収入割合
                        { _一般消費者        :: {-# UNPACK #-} !Double
                        , _民間企業          :: {-# UNPACK #-} !Double
                        , _官公庁            :: {-# UNPACK #-} !Double
                        , _海外取引          :: {-# UNPACK #-} !Double
                        , _同一企業          :: {-# UNPACK #-} !Double }
                        deriving (Show, Read, Eq, Generic)

instance NFData E相手先別収入割合

parserE相手先別収入割合 =  do
                string (T.pack "E相手先別収入割合 {")
                d1 <- f "_一般消費者 = "
                d2 <- f "_民間企業 = "
                d3 <- f "_官公庁 = "
                d4 <- f "_海外取引 = "
                d5 <- f "_同一企業 = "
                return (E相手先別収入割合 d1 d2 d3 d4 d5)

            where
            f :: String -> Parser Double
            f s =   do
                    string (T.pack s)
                    di <-  DAT.double
                    try (string (T.pack ", ")) <|> (string (T.pack "}"))
                    return di

-----------------------------------------------------------
-- ** 店舗形態
-----------------------------------------------------------
data E店舗形態_商業  = E各種商品小売店 | Eコンビニエンスストア |  Eドラッグストア | Eホームセンター
                deriving (Show, Read, Eq, Generic)

instance NFData E店舗形態_商業

parserE店舗形態_商業  =   f E各種商品小売店
                     <|>  f Eコンビニエンスストア
                     <|>  f Eドラッグストア
                     <|>  f Eホームセンター
                     where f s = try( string (T.pack (ushow s))) >> return s



-----------------------------------------------------------
-- ** 商品形態
-----------------------------------------------------------
data E商品形態 = E商品形態
               { _衣料品        :: {-# UNPACK #-} !Double
               , _飲食料品      :: {-# UNPACK #-} !Double
               , _その他商品    :: {-# UNPACK #-} !Double}
               deriving (Show, Read, Eq, Generic)

instance NFData E商品形態

parserE商品形態 =  do
                string (T.pack "E商品形態 {")
                d1 <- f "_衣料品 = "
                d2 <- f "_飲食料品 = "
                d3 <- f "_その他商品 = "
                return (E商品形態 d1 d2 d3)

            where
            f :: String -> Parser Double
            f s =   do
                    string (T.pack s)
                    di <-  DAT.double
                    try (string (T.pack ", ")) <|> (string (T.pack "}"))
                    return di

-----------------------------------------------------------
-- ** 販売形態
-----------------------------------------------------------
data E販売形態 = E販売形態
               { _店頭販売           :: {-# UNPACK #-} !Double
               , _訪問販売           :: {-# UNPACK #-} !Double
               , _通信販売           :: {-# UNPACK #-} !Double
               , _インターネット販売 :: {-# UNPACK #-} !Double
               , _自動販売機         :: {-# UNPACK #-} !Double
               , _その他販売         :: {-# UNPACK #-} !Double }
               deriving (Show, Read, Eq, Generic)

instance NFData E販売形態

parserE販売形態 =  do
                string (T.pack "E商品形態 {")
                d1 <- f "_店頭販売 = "
                d2 <- f "_訪問販売 = "
                d3 <- f "_通信販売 = "
                d4 <- f "_インターネット販売 = "
                d5 <- f "_自動販売機 = "
                d6 <- f "_その他販売 = "
                return (E販売形態 d1 d2 d3 d4 d5 d6)

            where
            f :: String -> Parser Double
            f s =   do
                    string (T.pack s)
                    di <-  DAT.double
                    try (string (T.pack ", ")) <|> (string (T.pack "}"))
                    return di

------------------------------------------------------------------
-- ** 工事種類
------------------------------------------------------------------
data E工事種類 = E工事種類 {_種類1 :: {-# UNPACK #-} !Text, _種類2 ::  {-# UNPACK #-} !Text }
                deriving (Read, Eq, Generic)
instance NFData E工事種類

instance Show E工事種類 where
    show (E工事種類 t1 t2) = "E工事種類 {_種類1 = " ++ ushow t1
                                                    ++ ", _種類2 = "
                                                    ++ ushow t2
                                                    ++ "}"

parserE工事種類 =  do
                string (T.pack "E工事種類 {")
                d1 <- f "_種類1 = "
                d2 <- f "_種類2 = "
                return (E工事種類 d1 d2)
            where
            f :: String -> Parser Text
            f s =   do
                    string (T.pack s)
                    di <-  quotedCell
                    try (string (T.pack ", ")) <|> (string (T.pack "}"))
                    return $! T.pack di



------------------------------------------------------
-- ** Cars
------------------------------------------------------
-- | タプルのリストのようなデータをこれで代替する
data Car  = Car { value :: {-# UNPACK #-} !Double
                , name  :: {-# UNPACK #-} !Text}
                deriving (Eq, Read, Generic)

instance Show Car where
    show (Car v n) = "Car {value = " ++ show v ++ ", name = " ++ ushow n ++ "}"

instance Ord Car where
    compare   x y     = compare   (value x) (value y)
    (<)       x y     = (<)       (value x) (value y)
    (<=)      x y     = (<=)      (value x) (value y)
    (>)       x y     = (>)       (value x) (value y)
    (>=)      x y     = (>=)      (value x) (value y)
    max x y | x >= y    = x
            | otherwise = y

    min x y | x <= y    = x
            | otherwise = y


instance NFData Car

{-# INLINE parseCar #-}
parseCar :: Parser Car
parseCar     =  string (T.pack "Car {value = ")
             >> DAT.double >>= \dl
             -> string (T.pack ", name = ")
             >> quotedCell >>= \tx
             -> char '}'
             >> return (Car dl (T.pack tx))


type Cars = V.Vector Car


-- | Car に対するValueの足し算
{-# INLINE addValueCar #-}
addValueCar :: Double -> Car -> Car
addValueCar dbl (Car v n) = Car (v + dbl) n

-- | Carのvalueに数値を乗ずる
multipleValueCar :: Double -> Car -> Car
multipleValueCar dl (Car v n) = Car (v * dl) n


-- | 名前無関係に合計値を出す
{-# INLINE sumCars #-}
sumCars :: Cars -> Double
sumCars cs = V.sum $! V.map value cs

-- | Null = 0 としてすべての値を足す
{-# INLINE sumValCars #-}
sumValCars :: ValCars -> Double
sumValCars Null        = 0
sumValCars (VCars cs ) = sumCars cs

-- | ValCarsの特定のnameであるCarの値を抽出する
getValofCars :: Text -> ValCars -> Double
getValofCars tx Null        = 0
getValofCars tx (VCars cs)  = V.sum $! V.map value $! V.filter (\x -> name x == tx) cs
getValofCars tx _           = 0


-- | Car の Mapによる変換
{-# INLINE lookupCarNameErr #-}
lookupCarNameErr :: Car -> Map Text Text -> Car
lookupCarNameErr ca mp = case Map.lookup (name ca) mp of
                         Just newName -> Car (value ca) newName
                         Nothing      -> error $ "error : lookupCarNameErr ; can not find " ++ T.unpack (name ca)

-- | Cars のMapによる変換
{-# INLINE lookupCarsNameErr #-}
lookupCarsNameErr :: Cars -> Map Text Text -> Cars
lookupCarsNameErr cs mp = V.map (\x -> lookupCarNameErr x mp ) cs

-- | Tuple から Carを作る
tupleToCar :: (Double, Text) -> Car
tupleToCar (d,t) = Car d t

{-# INLINE carFromList #-}
carFromList :: [(Double, Text)] -> Cars
carFromList xs = V.map tupleToCar $! V.fromList xs


-- | 同じName を持つCarを統合する
mergeSameNameCars :: Cars -> Cars
mergeSameNameCars cs | V.null cs            = cs
                     | V.length cs <= 1     = cs
                     | otherwise            = runST $ do
                                            culcMap  <- newSTRef Map.empty
                                            V.forM_ cs $ \c -> do
                                                tmpMap <-  readSTRef culcMap
                                                let n = name c
                                                case Map.lookup n tmpMap of
                                                    Just a   ->  modifySTRef culcMap (Map.insert n (a + (value c)))
                                                    Nothing  ->  modifySTRef culcMap (Map.insert n      (value c))

                                            resultMap <- readSTRef culcMap
                                            return $! carFromList $! L.map (\(x,y) -> (y,x)) $! Map.toList resultMap


-- | ValCars に Carsを結合する
appendVCars :: Cars -> ValCars -> ValCars
appendVCars cs   Null         | V.null cs                = Null
                              | otherwise                = VCars cs
appendVCars cs1  (VCars cs2)  | V.null ((V.++) cs1 cs2)  = Null
                              | otherwise                = VCars $! cs1 V.++ cs2



-- | 最大のCarの nameを取得する
--
--   Cars が null のときはT.emptyを返す

{-# INLINE vmaximumNameWithoutErr #-}
vmaximumNameWithoutErr :: Cars -> Text
vmaximumNameWithoutErr cs   | V.null cs = T.empty
                            | otherwise = name $! V.maximum cs

-- | 最大の項目のCarを取得
--
-- 最大値が重複していた場合は全て返す
{-# INLINE vmaximumsWithoutErr #-}
vmaximumsWithoutErr :: Cars -> [Car]
vmaximumsWithoutErr cs  | V.null cs = []
                        | otherwise = runST $ do
                                !maxCars     <- newSTRef [V.head cs]
                                !tmpMaxValue <- newSTRef ((value . V.head) cs :: Double)

                                V.forM_ (V.tail cs) $ \c -> do
                                    curValue <- readSTRef tmpMaxValue
                                    when ( (value c) > curValue)
                                         (  writeSTRef tmpMaxValue (value c)
                                         >> writeSTRef maxCars     [c] )

                                    when ( (value c) == curValue)
                                         ( modifySTRef maxCars (c:))

                                readSTRef maxCars >>= return


-- | value が最大のCarのnameを取得
--
-- 最大値が重複していた場合は全て返す
vmaximumNamesWithoutErr :: Cars -> [Text]
vmaximumNamesWithoutErr cs = L.map name $! vmaximumsWithoutErr cs



















