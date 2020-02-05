mean xs = sum / len
 where
  step (s, l) x = (s+x, l+1)
  (sum, len) = foldl step (0, 0) xs