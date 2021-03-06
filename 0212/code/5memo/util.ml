open Syntax

(* op とハンドラを受け取って、ハンドラで op が定義されていればその情報を返す *)
let search_op (op : string) ({ops} : h) : (string * string * e) option =
  try
    let (_, x, k, e) = List.find (fun (name, x, k, e) -> name = op) ops in
    Some (x, k, e)
  with Not_found -> None

let rec subst_v (v : v) (pairs : (string * v) list) : v = match v with
  | Var (x) -> (try List.assoc x pairs with Not_found -> v)
  | Fun (x, e) -> if List.mem_assoc x pairs then v else Fun (x, subst e pairs)
  | Cont (x, (k, k2), f) -> Cont (x, (subst_k k pairs, subst_k2 k2 pairs), f)

and subst_k (k : k) (pairs : (string * v) list) : k = match k with
  | FId -> FId
  | FApp2 (e1, k) -> FApp2 (subst e1 pairs, subst_k k pairs)
  | FApp1 (k, v2) -> FApp1 (subst_k k pairs, subst_v v2 pairs)
  | FOp (name, k) -> FOp (name, subst_k k pairs)

and subst_k2 (k2 : k2) (pairs : (string * v) list) : k2 = match k2 with
  | GId -> GId
  | GHandle (h, k, k2) ->
    GHandle (subst_h h pairs, subst_k k pairs, subst_k2 k2 pairs)

and subst_h ({return; ops} : h) (pairs : (string * v) list) : h =
  let new_return = match return with (x, e) ->
      if List.mem_assoc x pairs then return
      else (x, subst e pairs) in
  let new_ops =
    List.map
      (fun ((name, x, k, e) as op) ->
         if List.mem_assoc x pairs || List.mem_assoc k pairs then op
         else (name, x, k, subst e pairs))
      ops in
  {return = new_return; ops = new_ops}

and subst (e : e) (pairs : (string * v) list) : e = match e with
  | Val (v) -> Val (subst_v v pairs)
  | App (e1, e2) -> App (subst e1 pairs, subst e2 pairs)
  | Op (name, e) -> Op (name, subst e pairs)
  | With (h, e) -> With (subst_h h pairs, subst e pairs)

(* プログラム内で使われている変数のリストを格納する変数 *)
let var_names = ref []

(* 新しい変数を作成する時の名前の例のリスト *)
let var_name_examples =
  let rec a_to_w i =
    if i > 119 then [] else Char.escaped (Char.chr i) :: a_to_w (i + 1) in
  let rec x_to_z i =
    if i > 122 then a_to_w 97
    else Char.escaped (Char.chr i) :: x_to_z (i + 1) in
  x_to_z 120

(* 使われている変数リストに新しい変数名を追加する *)
let add_var_name (var : string) : unit =
  let current_var_names = !var_names in
  if List.mem var current_var_names
  then ()
  else var_names := var :: current_var_names

let rec record_var_name : e -> unit = function
  | Val (v) -> record_var_name_value v
  | App (e1, e2) -> record_var_name e1; record_var_name e2
  | Op (name, e) -> record_var_name e
  | With (h, e2) -> record_var_name_handler h; record_var_name e2

and record_var_name_value : v -> unit = function
  | Var (x) -> ()
  | Fun (x, e) -> add_var_name x; record_var_name e
  | Cont (x, k, f) -> ()

and record_var_name_handler : h -> unit = fun {return; ops} ->
  begin
    match return with (x, e) -> add_var_name x; record_var_name e
  end;
  begin
    List.iter
      (fun (op, x, k, e) -> add_var_name x; add_var_name k; record_var_name e)
      ops
  end

(* プログラム内でまだ使われていない変数名を生成して返す *)
let gen_var_name () =
  let new_var =
    try List.find (fun var -> not (List.mem var !var_names)) var_name_examples
    with Not_found -> "x" ^ string_of_int (List.length !var_names) in
  var_names := new_var :: !var_names;
  new_var

