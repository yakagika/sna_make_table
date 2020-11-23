
{-# LANGUAGE  BangPatterns, StrictData #-}

import qualified Data.Text.Lazy     as TL
import qualified Data.Text.Lazy.IO  as TLO 
import qualified Data.List          as L
import CSV.Text.Lazy
import System.IO
import Debug.Trace

test = "testest"
rowLen24 = 778
rowLen28 = 355

multi :: (a -> a) -> Int -> (a -> a)
multi f 1 = f
multi f n | n <= 0    =  error "multipled minus" 
          | otherwise =  f . (multi f (n - 1))

fixLength :: FilePath -> Int -> IO ()
fixLength path int  =  openFile path ReadMode >>= \rHandle
                    -> openFile (((multi init 4) path) ++ "FixedTest.csv") WriteMode >>= \wHandle
                    -> loop rHandle wHandle
    where 
    loop :: Handle -> Handle -> IO ()
    loop rHandle wHandle 
        = hIsEOF rHandle >>= \eof
        -> if   eof 
                then return()
                else head <$> parseCSVErr <$> TLO.hGetLine rHandle >>= \line 
                -> if (length  line) >= int 
                        then  hPutCsvLn wHandle line 
                              >> loop rHandle wHandle
                        
                        else let addNum = int - (length line) 
                             in  let !added  = line ++ replicate (trace (show addNum) addNum) TL.empty 
                             in  ((TLO.hPutStrLn wHandle).TL.concat.(L.intersperse (TL.pack ","))) added 
                             >>  loop rHandle wHandle

main = do 
--    fixLength "Data/Record/K24.csv" rowLen24
    fixLength "Data/Record/K28.csv" rowLen28
