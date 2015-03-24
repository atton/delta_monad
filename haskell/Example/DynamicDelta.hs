module Example.DynamicDelta where

import Delta
import Data.Dynamic

val :: Delta Dynamic
val = Delta (toDyn True) (Mono (toDyn ([1,2,3,2,1] :: [Int])))

func :: Dynamic -> Delta Dynamic
func x = let funcToBool = toDyn not
             funcToList = toDyn (sum :: [Int] -> Int)
         in
            Delta (dynApp funcToBool x) (Mono (dynApp funcToList x))

firstVal :: Delta Dynamic -> Maybe Bool
firstVal = fromDynamic . headDelta

secondVal :: Delta Dynamic -> Maybe Int
secondVal = fromDynamic . headDelta . tailDelta
