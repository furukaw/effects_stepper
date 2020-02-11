(* コンテキスト k2_in の外側にフレーム GHandle (h, k_out, k2_out) を付加する *)
let rec compose_k2 k2_in h (k_out, k2_out) =
  match k2_in with
  | GId -> GHandle (h, k_out, k2_out)
  | GHandle (h', k', k2') -> GHandle (h', k', compose_k2 k2' h (k_out, k2_out))
