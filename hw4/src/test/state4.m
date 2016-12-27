let f = proc (x) proc (y) ((set x = x + 1); x - y) in
  ((f 44) 33)
