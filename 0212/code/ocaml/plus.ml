effect E : int -> int;;
try 1 + (perform (E 2)) + (perform (E 4)) with
| effect (E n) k -> continue k n
