
-- Program to make test data

import CSV.Text.Lazy
import qualified    Control.Monad.Parallel          as CMP
import qualified    Data.Text.Lazy.IO               as TLO
import qualified    Data.Text.Lazy                  as TL
import VTable.Compliation.Conversion
import VTable.Data.Structure
import System.Environment (getArgs)


makeTestDataFilePath filePath  num = do
    originalFile <- TLO.readFile filePath
    let cuttedFile  = TL.unlines $ take num $ TL.lines originalFile
        output = ((init.init.init.init)  filePath)  ++ "ForTest.csv" 
    print $ "Converting " ++ filePath ++ " ..."
    TLO.writeFile output cuttedFile
    print $ "Finished conversion of " ++ filePath++ "!"


main = do
    args <- getArgs
    let file =  args !! 0
    let year  = (read (args !! 1) :: Int)
    let num   = (read (args !! 2) :: Int)
    -- makeTestDataFilePath file year
    CMP.forM_   (filter (\x -> getFileYear x == year) [SB28 .. KMP28])
                (\x -> makeTestDataFilePath ((originalToConverted . getRecordFilePath) x) num)