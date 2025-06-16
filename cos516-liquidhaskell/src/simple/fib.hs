import System.Environment   

fib :: Word -> Word
fib 0 = 0
fib 1 = 1
fib n = fib (n-1) + fib (n-2)

fib10 = [0, 1, 1, 2, 3, 5, 8, 13, 21, 34]
fib10' = [fib x | x <- [0..9]]
test = fib10 == fib10'

main :: IO ()
main = do
  args <- getArgs
  putStrLn "hello, world"
  print (fib 3)
