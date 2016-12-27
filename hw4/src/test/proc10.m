let swap = proc (x) proc (y)
            let temp = x in
              (set x = y; set y = temp) in
let a = 33 in
let b = 44 in
  (((swap <a>) <b>); b)
