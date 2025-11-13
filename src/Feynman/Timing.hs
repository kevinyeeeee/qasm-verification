module Feynman.Timing where
import Data.IORef
import System.CPUTime
import GHC.IO
import Numeric (showFFloat)
{- Please do not look at our shame -}

formatFloatN floatNum numOfDecimals = showFFloat (Just numOfDecimals) floatNum ""

simulationTime :: IORef Double
simulationTime = unsafePerformIO (newIORef 0)

addSimulationTime :: Integer -> Integer -> IO ()
addSimulationTime start end = do
        totalTime <- readIORef simulationTime
        let runTime = (fromIntegral $ end - start) / 10^9
        writeIORef simulationTime (runTime+totalTime)

{-timeSimulation :: (() -> a) -> a 
timeSimulation f = 
    unsafePerformIO $! do
        start <- getCPUTime
        let res = f ()
        end <- res `seq` getCPUTime
        return (addSimulationTime runTime `seq` res)-}

getStringSimulationTime :: IO String
getStringSimulationTime = do
    t <- readIORef simulationTime
    return (formatFloatN t 3)

checkingTime :: IORef Double
checkingTime = unsafePerformIO (newIORef 0.00000000000000001)

addCheckingTime :: Integer -> Integer -> IO ()
addCheckingTime start end = do
        totalTime <- readIORef checkingTime
        let runTime = (fromIntegral $ end - start) / 10^9
        writeIORef checkingTime (runTime+totalTime)

{-timechecking :: (() -> a) -> a 
timechecking f = 
    unsafePerformIO $! do
        start <- getCPUTime
        let res = f ()
        end <- res `seq` getCPUTime
        return (addcheckingTime runTime `seq` res)-}

getStringCheckingTime :: IO String
getStringCheckingTime = do
    t <- readIORef checkingTime
    return (formatFloatN t 3)