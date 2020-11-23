{-# LANGUAGE  BangPatterns,OverloadedStrings, StrictData #-}

-- 石油卸売業を取得するだけのもの
-- 事前格付けの小分類が533なら書き出し，そうでないならとばす

import qualified    Data.Text                       as T
import              Data.Text                       (Text)
import qualified    Data.Text.IO                    as TO
import              CSV.Text
import qualified    CSV.Text                        as CSV
import              VTable.Data.Structure
import qualified    VTable.Data.Structure           as VDS
import              VTable.Data.Classification
import qualified    VTable.Data.Classification      as VDC
import              VTable.Compliation.Conversion
import qualified    VTable.Compliation.Conversion   as VCC
import              System.IO


type InputFile  = String
type OutPutFile = String


oilGetter :: Main.InputFile -> OutputFile  -> IO ()
oilGetter input output = do
    rHandle <- openFile input  ReadMode
    wHandle <- openFile output WriteMode

    hPutCsvLn wHandle VDS.hKC28
    loop rHandle wHandle
    hClose rHandle
    hClose wHandle


    where
    -- 事前格付小分類のHeader
    small       = "(事)産業小分類"
    skcHeader   = VDS.getHeader KC28
    target      = "533" :: T.Text

    isTarget :: Text -> Bool
    isTarget tx | tx == target = True
                | otherwise    = False


    loop :: Handle -> Handle -> IO ()
    loop rHandle wHandle    
        = hIsEOF rHandle >>= \eof 
        -> case eof  of 
            True  ->    return () 
            False ->    head 
                        <$> parseCSVErr
                        <$> TO.hGetLine rHandle >>= \ !line
                        ->  case (isTarget (VCC.projFrom small skcHeader line)) of
                            False -> loop rHandle wHandle
                            True  -> hPutCsvLn wHandle line
                                  >> loop rHandle wHandle


main = do 
    oilGetter (VDS.getRecordFilePath KC28) "test.csv"
