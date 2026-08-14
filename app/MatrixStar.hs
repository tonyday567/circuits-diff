module MatrixStar (runMatrixStarTests) where

import Circuit.Mat.Dense (Matrix (..), fromLists, starMatrix, toLists)
import NumHask.Free.Carriers (FieldStar (..), MinPlus (..), Warshall (..))
import System.Exit (exitFailure)
import Prelude

assert :: String -> Bool -> IO ()
assert msg ok =
  if ok
    then putStrLn ("  PASS " ++ msg)
    else do
      putStrLn ("  FAIL " ++ msg)
      exitFailure

runMatrixStarTests :: IO ()
runMatrixStarTests = do
  putStrLn "list-matrix star tests"

  assert "Warshall transitive closure" $
    let m = fromLists [[Warshall False, Warshall True], [Warshall False, Warshall False]]
     in starMatrix m == fromLists [[Warshall True, Warshall True], [Warshall False, Warshall True]]

  assert "Floyd-Warshall shortest paths" $
    let inf = MinPlus (1 / 0)
        m = fromLists [[MinPlus 0, MinPlus 3, inf], [inf, MinPlus 0, MinPlus 1], [MinPlus 2, inf, MinPlus 0]]
        expected = fromLists [[MinPlus 0, MinPlus 3, MinPlus 4], [MinPlus 3, MinPlus 0, MinPlus 1], [MinPlus 2, MinPlus 5, MinPlus 0]]
     in starMatrix m == expected

  assert "Field star matrix inversion" $
    let m = fromLists [[FieldStar 0.1, FieldStar 0.2], [FieldStar 0.3, FieldStar 0.1]]
        rows = map (map (\(FieldStar x) -> x)) (toLists (starMatrix m))
     in case rows of
          [[a, b], [c, d]] ->
            abs (a - 1.2) < 1e-10
              && abs (b - 0.2666666666666667) < 1e-10
              && abs (c - 0.4) < 1e-10
              && abs (d - 1.2) < 1e-10
          _ -> False

  assert "starMatrix empty matrix" $
    let m = fromLists [] :: Matrix Warshall
     in starMatrix m == m
