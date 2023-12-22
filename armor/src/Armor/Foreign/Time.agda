open import Armor.Prelude

module Armor.Foreign.Time where

{-# FOREIGN GHC import qualified Data.Text #-}
{-# FOREIGN GHC import Data.Time #-}
{-# FOREIGN GHC import Data.Time.Clock #-}
{-# FOREIGN GHC import Data.Time.Calendar.OrdinalDate #-}
{-# FOREIGN GHC import Data.Time.Calendar.MonthDay #-}
{-# FOREIGN GHC import Data.Time.LocalTime #-}

{-# FOREIGN GHC

year :: UTCTime -> Integer
year = fst . toOrdinalDate . utctDay

month :: UTCTime -> Integer
month x = toInteger . fst . dayOfYearToMonthAndDay (isLeapYear . year $ x) . snd . toOrdinalDate . utctDay $ x

day :: UTCTime -> Integer
day x = toInteger . snd . dayOfYearToMonthAndDay (isLeapYear . year $ x) . snd . toOrdinalDate . utctDay $ x

hour :: UTCTime -> Integer
hour = toInteger . todHour . timeToTimeOfDay . utctDayTime

minute :: UTCTime -> Integer
minute = toInteger . todMin . timeToTimeOfDay . utctDayTime

second :: UTCTime -> Integer
second = fst . properFraction . todSec . timeToTimeOfDay . utctDayTime

showTime :: UTCTime -> Data.Text.Text
showTime = Data.Text.pack . show
#-}

postulate
  UTCTime Day : Set

postulate
  year   : UTCTime → ℕ
  month  : UTCTime → ℕ
  day    : UTCTime → ℕ
  hour   : UTCTime → ℕ
  minute : UTCTime → ℕ
  second : UTCTime → ℕ
  showTime : UTCTime → String

{-# COMPILE GHC UTCTime    = type UTCTime #-}
{-# COMPILE GHC Day        = type Day #-}
{-# COMPILE GHC year   = year  #-}
{-# COMPILE GHC month  = month  #-}
{-# COMPILE GHC day    = day  #-}
{-# COMPILE GHC hour   = hour  #-}
{-# COMPILE GHC minute = minute  #-}
{-# COMPILE GHC second = second  #-}
{-# COMPILE GHC showTime = showTime  #-}
