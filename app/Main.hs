

-- 全体的な処理はこのプログラムで完結する
--
-- -N18 - 20 , -A4G を想定




import              VTable.Compilation
import qualified    VTable.Compilation              as VC

import              VTable.Compilation.Conversion
import qualified    VTable.Compilation.Conversion   as VCC

import              VTable.Data.Structure
import qualified    VTable.Data.Structure           as VDS

import              System.Environment (getArgs)
import qualified    Control.Monad.Parallel          as CMP


main = do
    args <- getArgs
    let year = (read (args !! 0) :: Int)
    -- 下処理
    -- VCC.convertWhole year "Data/Record/Merge24New.csv"
    VDS.mergeFilesMemEfficient  "Data/Record/Merge24New.csv" year
    let maxRowNum = 4433146
    -- let maxRowNum = 100
    VC.compileVTable "Data/Record/Merge24New.csv" maxRowNum year

