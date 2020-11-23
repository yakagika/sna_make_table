

import qualified    Data.Vector                     as V
import qualified    Data.Text                       as T
import              Data.Text                       (Text)

import              Control.Monad.IO.Class (liftIO, MonadIO)
import              Data.Array.IArray
import              Data.Array.ST
import              Data.Array.IO

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


convertMining :: InputFile -> IO ()
convertMining inputFile = runConduitRes $ sourceCensus inputFile .| f鉱業変換 .| sinkCensus 4433146 "Data/Record/鉱業変換.csv"

f鉱業変換 :: (MonadIO m) => ConduitT IOCensusRow IOCensusRow m ()
f鉱業変換 = do
    maybeIcr <- await
    case maybeIcr of
        Nothing  -> return ()
        Just icr -> liftIO (readArray icr H生産_鉱業_数量) >>= \ quantity
                 -> liftIO (readArray icr H生産_鉱業_金額) >>= \ money
                 -> case (quantity, money) of
                        (Null, Null)            -> yield icr >> f鉱業変換

                        (Null, VCars ms)        -> liftIO (writeArray icr H生産_鉱業_金額 (VCars (f ms)))
                                                >> yield icr >> f鉱業変換

                        (VCars qs, Null)        -> liftIO (writeArray icr H生産_鉱業_数量 (VCars (f qs)))
                                                >> yield icr >> f鉱業変換

                        (VCars qs, VCars ms)    -> liftIO (writeArray icr H生産_鉱業_数量 (VCars (f qs)))
                                                >> liftIO (writeArray icr H生産_鉱業_金額 (VCars (f ms)))
                                                >> yield icr >> f鉱業変換

    where
    f :: Cars -> Cars
    f = V.map $ \(Car v n) ->  Car v $ T.append (T.pack "05") (T.init (T.tail n))

main = do
    convertMining "Data/Record/Merge24.csv"
