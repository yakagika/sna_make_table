

{-# LANGUAGE  BangPatterns #-}

import qualified Data.Text.Lazy as TL
import qualified Data.Text.Lazy.IO as TLO
import CSVAttoParserTLazy

import              Control.Parallel.Strategies     hiding (parMap)
import              Control.Parallel

parMap :: (a -> b) -> [a] -> Eval [b]
parMap f [] = return []
parMap f !(a:as)  = do
    b  <- rpar (f a)
    bs <- parMap f as
    return (b:bs) 

main = do 
    x <- TLO.readFile "Data/Record/K28Fixed.csv"
    print $! minimum $! runEval $! parMap (length . head . parseCSVTErr ) $! TL.lines x