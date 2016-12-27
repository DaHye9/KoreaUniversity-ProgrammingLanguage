let counter = 0 in
let f = proc (x) (set counter = counter + 1; counter) in
let a = (f 0) in
let b = (f 0) in
  (a-b)

