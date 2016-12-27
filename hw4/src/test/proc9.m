let f = proc (x) (set x = 44) in
let g = proc (y) (f <y>) in
let z = 55 in 
  ((g <z>); z)
