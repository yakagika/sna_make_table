import V
import VDS
import System.Environment (getArgs)

main = do 
    args <- getArgs
    let year = (read (args !! 0) :: Int)
    let input  = "Data/testMerge24.csv"
    



    full価格 input 6108738  year