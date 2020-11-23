import VTable.Compliation
import VTable.Data.Structure
import System.Environment (getArgs)

main = do 
    args <- getArgs
    let year = (read (args !! 0) :: Int)
    let input  = "Data/testMerge24.csv"

    full産業格付 input 6108738  year