{-# LANGUAGE BangPatterns      #-}
{-# LANGUAGE NamedFieldPuns    #-}
{-# LANGUAGE OverloadedStrings #-}

-- TODO explain what this module does.
module Main (main) where

import           Control.Monad (void, when)
import           Control.Monad.Extra (ifM, whenM)
import qualified Data.Text as Text
import qualified Data.Text.IO as Text.IO
import qualified Data.Text.Read as Text.Read
import           Options.Applicative (Parser, execParser, fullDesc, help,
                     helper, info, long, metavar, progDesc, short, strOption,
                     (<**>))
import           System.Exit (exitFailure)
import           System.IO (IOMode (ReadMode), hIsEOF, withFile)

import           Graphics.Vega.VegaLite (AxisProperty (AxGrid),
                     Channel (ChX, ChY), Data, DataColumn, DataValues (Numbers),
                     Mark (Point, Rule), MarkChannel (MName, MmType),
                     MarkProperty (MStroke, MStrokeDash),
                     Measurement (Nominal, Quantitative), Position (X, Y),
                     PositionChannel (PAxis, PName, PScale, PmType),
                     ScaleProperty (SZero), Selection (Interval),
                     SelectionProperty (BindScales, Encodings),
                     TextChannel (TName, TmType), VegaLite, asSpec, color,
                     dataColumn, dataFromColumns, encoding, fold, height, layer,
                     mark, position, select, selection, toHtmlFile, toVegaLite,
                     tooltips, transform, width)

main :: IO ()
main = do
    CmdLineArgs {logFile} <- getCmdLineArgs

    slotDataPoints <- dataRowsToSlotDataPoints <$> logFileToDataRows logFile

    -- TODO use a more robust method to detect which measurements are true
    -- outliers. It could be as simple as using the values outside the upper
    -- interquartile range (as we are not interested in slots that were
    -- processed "faster than" normal).
    --
    -- For now we keep only measurements that took more 0.025 seconds.
    let slowSlots = filter ((>= 25000) . totalTime ) slotDataPoints

    let maxSampleSize = 10000
    when (maxSampleSize < length slowSlots) $ do
      putStrLn "Sample too large."
      putStrLn $ "Due to the performance of vega-lite "
               <> "we cap the size of the sample we plot to "
               <> show maxSampleSize
               <> " elements"
      void exitFailure

    toHtmlFile "slow-slots-processing-times.html" $
      timesToVegaLite slowSlots
                      (EpochMarkers $ firstSlotOfEachEpoch `within` slotDataPoints)
                      (EraMarkers   $ firstSlotOfEachEra   `within` slotDataPoints)

  where
    -- The first shelley epoch was 208, and it began in slot 4492800. There are
    -- 10k/f = 2160 * 10 * 20 = 432000 slots in each Shelley epoch.
    firstSlotOfEachEpoch :: [Int]
    firstSlotOfEachEpoch = [ 4492800 + i * 432000 | i <- [0 ..]  ]

    -- See https://github.com/input-output-hk/cardano-ledger/wiki/First-Block-of-Each-Era
    firstSlotOfEachEra :: [Int]
    firstSlotOfEachEra = [ 4492800  -- Shelley
                         , 16588800 -- Allegra
                         , 23068800 -- Mary
                         , 39916975 -- Alonzo
                         , 43372972 -- Alonzo' (intra-era hardfork)
                         , 72316896 -- Babbage
                         ]

    within slots sample
        = takeWhile (<= maximumSlotInSample)
        . dropWhile (<= minimumSlotInSample)
        $ slots
      where
        -- TODO: is speed is critical we should probably traverse the list only once
        minimumSlotInSample = minimum $ fmap slot sample
        maximumSlotInSample = maximum $ fmap slot sample


{-------------------------------------------------------------------------------
 Data exchange format specification
-------------------------------------------------------------------------------}

data SlotDataPoint =
    SlotDataPoint
      { slot      :: Int
      , totalTime :: Int
      , mut       :: Int
      , gc        :: Int
      }

data EpochMarkers a = EpochMarkers [a]

data EraMarkers a = EraMarkers [a]

{-------------------------------------------------------------------------------
 Data file parsing into @SlotDataPoint@s

 FIXME this step should parse 'SlotDataPoint's directly, which should be output
 by the benchmarking program. As it stands the code in this section is super
 brittle.
 -------------------------------------------------------------------------------}

-- | Parse the log file into a list of lists, where each element of the outer
-- list represents a data-row.
logFileToDataRows :: FilePath -> IO [[Int]]
logFileToDataRows aLogFile =
    withFile aLogFile ReadMode $ \handle -> do
        -- Header processing
        --
        -- FIXME: this will not be necessary if the benchmarking program encodes
        -- to the interchange format.
        whenM (hIsEOF handle) $ putStrLn "Expecting headers expected" >> exitFailure
        -- We simply discard the first line
        _ <- Text.IO.hGetLine handle
        -- Values processing
        let loop !acc = do
                ifM (hIsEOF handle)
                    ( -- We appended each new line to the front of the
                      -- accumulator, therefore we have to reverse the resulting
                      -- accumulator.
                      pure (reverse acc)
                    )
                    (do
                        line <- Text.words <$> Text.IO.hGetLine handle
                        loop (line:acc)
                    )

        rawValues <- loop []
        let textToInt = either error fst . Text.Read.decimal

        pure $ fmap (fmap textToInt) rawValues

dataRowsToSlotDataPoints :: [[Int]] -> [SlotDataPoint]
dataRowsToSlotDataPoints = fmap toSlotDataPoint
  where
    toSlotDataPoint x = SlotDataPoint (x !! 0) (x !! 2) (x !! 3) (x !! 4)

{-------------------------------------------------------------------------------
 Plotting via hvega
-------------------------------------------------------------------------------}

-- | Convert the execution times into a vega-lite plot specification.
timesToVegaLite
  :: [SlotDataPoint] -> EpochMarkers Int -> EraMarkers Int -> VegaLite
timesToVegaLite slotDataPoints (EpochMarkers epochMarkers) (EraMarkers eraMarkers)
    -- TODO: add types to local bindings
    = toVegaLite
    $ [ dataColumns []
      , trans []
      , layer (map asSpec [individualTimes, totalTimes, epochs, eras])
      , height 400
      , width 1200
      ]

  where
    -- TODO: I should probably use the string rep of the field names
    dataColumns :: [DataColumn] -> Data
    dataColumns = dataFromColumns []
                . dataColumn "slot"      (Numbers $ fmap (fromIntegral . slot) slotDataPoints)
                . dataColumn "totalTime" (Numbers $ fmap (fromIntegral . totalTime) slotDataPoints)
                . dataColumn "mut"       (Numbers $ fmap (fromIntegral . mut) slotDataPoints)
                . dataColumn "gc"        (Numbers $ fmap (fromIntegral . gc) slotDataPoints)

    -- We need to fold the fields below to make them appear in the same scatter plot.
    trans = transform
          . fold [ "totalTime", "mut", "gc"]

    individualTimes = [ mark Point []
                      , enc []
                      ]
      where
        enc = encoding
            . position X [ PName "slot",  PmType Quantitative
                         , PScale scaleOpts
                         , PAxis [AxGrid False]
                         ]
            . position Y [ PName "value", PmType Quantitative] -- "value" comes from the fold transform
            . color      [ MName "key", MmType Nominal ]       -- "key" also comes from the fold transform
            . tooltips   [ [ TName "slot", TmType Nominal ]
                         , [ TName "value", TmType Nominal ]
                         ]
            where
              scaleOpts = [ SZero False ]

    totalTimes = [ mark Rule [ MStrokeDash [ 3 ]
                             , MStroke "grey"
                             ]
                 ,   encoding
                   . position X [ PName "slot",       PmType Quantitative]
                   . position Y [ PName "totalTime", PmType Quantitative ]
                   $ []
                 , sel []
                 ]
      where
        sel = selection
            . select "picked" Interval [ Encodings [ ChX, ChY ], BindScales ]

    epochs = [   dataFromColumns []
               . dataColumn "epoch" (Numbers $ fmap fromIntegral epochMarkers)
               $ []
             , mark Rule [ MStrokeDash [ 1 ]
                         , MStroke "orange"
                         ]
             ,   encoding
               . position X [ PName "epoch", PmType Quantitative]
               $ []
             ]

    eras = [   dataFromColumns []
               . dataColumn "era" (Numbers $ fmap fromIntegral eraMarkers)
               $ []
             , mark Rule [ MStroke "red"
                         ]
             ,   encoding
               . position X [ PName "era", PmType Quantitative]
               $ []
             ]

{-------------------------------------------------------------------------------
 Command line arguments parsing
-------------------------------------------------------------------------------}

newtype CmdLineArgs = CmdLineArgs {
    -- | Path to the log file that will be used for plotting
    logFile :: FilePath
    } deriving (Show)

getCmdLineArgs :: IO CmdLineArgs
getCmdLineArgs = execParser opts
  where
    opts = info (parseCmdLineArgs <**> helper)
                (mconcat [ fullDesc, progDesc "Plot the results of the db-analyser" ])


parseCmdLineArgs :: Parser CmdLineArgs
parseCmdLineArgs = CmdLineArgs
                <$> logFileParser
  where
    logFileParser =
        strOption (mconcat [
            long "log-file"
          , short 'f'
          , help "Path to the log file that will be used for plotting"
          , metavar "PATH"
          ])
