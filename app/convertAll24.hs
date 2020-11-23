
-- Program for convert all data

{-# LANGUAGE  BangPatterns, StrictData, Strict #-}

import System.IO
import Control.Monad
import VTable.Compilation.Conversion
import VTable.Data.Classification
import VTable.Data.Structure
import qualified Control.Monad.Parallel as CMP



main = do
    let fileTypes = filter (\x -> getFileYear x == 24) [SB28 .. KMI28]
    CMP.forM_ fileTypes $ \ fileType -> do
        let output = ((init.init.init.init)  (getRecordFilePath fileType)) ++ "Converted.csv"
        print $ "Converting " ++ show fileType ++ " ..."
        convertData fileType output
        print $ "Finished conversion of " ++ show fileType ++ "!"
    print "Start converting KMP ..."
    convertKMP
    print "Start mergeing converted files"
    mergeFiles "Data/Merge24.csv" 24
    print "finished!"