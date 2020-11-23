{-# LANGUAGE BangPatterns, StrictData, Strict #-}

import VTable.Compliation
import VTable.Compliation.Conversion
import VTable.Data.Structure
import System.Environment (getArgs)
import qualified Data.Map.Strict as Map
import              Data.Conduit 
import qualified    Data.Conduit.List               as CL
import qualified    Data.Conduit.Binary             as CB hiding (sequence, dropWhile, sourceFile)
import qualified    Data.Conduit.Combinators        as CC
import              Data.IORef


main =  let year = 24
    in  let inputFile = "Data/Merge24ForTest.csv"
    in  let maxRowNum = 10000
    in  let tmpFile   = "Data/tempFileForTest.csv"
    in  let tmpFile2  = "Data/tempFileForTest2.csv"
    in print "statr first step "
    >> runConduitRes    (sourceCensus inputFile  
                        .| f在庫品評価調整
                        .| f産業格付_特殊な方法 year
                        .| f不適当分削除
                        .| f産業格付_一般的な方法 year
                        .| f価格変換 year
                        .| sinkCensus maxRowNum tmpFile)
    >>  print "end first step. And start culculation of Industry weight map" 
    >>  getWeightAndLink tmpFile                                                >>= \ (!iwm, !edm) 
    ->  newIORef Map.empty                                                      >>= \ !empDenomiMap
    ->  runConduitRes (sourceCensus  tmpFile  .| getDenomiMap iwm empDenomiMap) >>= \ !denomi 
    ->  newIORef Map.empty                                                      >>= \ !empToMakeMarginMap
    ->  newIORef []                                                             >>= \ !nullList
    ->  print "end second step. And start division" 
    >>  runConduitRes  (sourceCensus tmpFile  .| f企業分割 iwm edm denomi 
                                              .| f商業マージン処理 empToMakeMarginMap nullList
                                              .| f企業内取引削除 year
                                              .| sinkCensus maxRowNum tmpFile2)
