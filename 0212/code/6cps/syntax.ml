(* 値 *)
type v = Var of string      (* x *)
       | Fun of string * e  (* fun x -> e *)
       | Cont of string * (c * c2) * ((c * k) -> k) (* 継続 *)
(* ハンドラ *)
and h = {
  return : string * e;                       (* handler {return x -> e,      *)
  ops : (string * string * string * e) list  (*          op(x; k) -> e, ...} *)
}
(* 式 *)
and e = Val of v          (* v *)
      | App of e * e      (* e e *)
      | Op of string * e  (* op e *)
      | With of h * e     (* with h handle e *)
(* handle 内の実行結果 *)
and a = Return of v                          (* 値になった *)
      | OpCall of string * v * (c * c2) * k  (* オペレーションが呼び出された *)
(* handle 内のメタ継続 *)
and k = v -> c2 -> a
(* handle 内のコンテキスト *)
and c = FId                (* [.] *)
      | FApp2 of e * c     (* [e [.]] *)
      | FApp1 of c * v     (* [[.] v] *)
      | FOp of string * c  (* [op [.]] *)
(* 全体のコンテキスト *)
and c2 = GId
       | GHandle of h * c * c2


type cont = c * c2

let hole : e = Val (Var "8")

(* 式と handle 節内のコンテキスト情報を受け取ってhandle 節の式を再構成する *)
let rec plug_in_handle (e : e) (c : c) : e = match c with
  | FId -> e
  | FApp2 (e1, c) -> plug_in_handle (App (e1, e)) c
  | FApp1 (c, v2) -> plug_in_handle (App (e, Val v2)) c
  | FOp (name, c) -> plug_in_handle (Op (name, e)) c

(* 式と handle 節内と外のコンテキスト情報のペアを受け取ってプログラム全体を再構成する *)
let rec plug_all (e : e) ((c, c2) : (c * c2)) : e =
  let e_in_handle = plug_in_handle e c in
  match c2 with
  | GId -> e_in_handle
  | GHandle (h, c, c2) ->
    let e_handle = With (h, e_in_handle) in
    plug_all e_handle (c, c2)

(* 値を文字列にする関数 *)
let rec v_to_string (v : v) : string = match v with
  | Var (x) -> x
  | Fun (x, e) -> "(fun " ^ x ^ " -> " ^ e_to_string e ^ ")"
  | Cont (x, (k, k2), f) ->
    "(fun " ^ x ^ " => " ^ e_to_string (plug_all (Val (Var x)) (k, k2)) ^ ")"

and h_to_string : h -> string = fun {return; ops} ->
  let return_strs = match return with (x, e) ->
    ["return " ^ x ^ " -> " ^ e_to_string e] in
  let op_strs =
    List.map
      (fun (name, x, k, e) ->
         name ^ "(" ^ x ^ "; " ^ k ^ ") -> " ^ e_to_string e)
      ops in
  match return_strs @ op_strs with
  | [] -> ""
  | first :: rest ->
    List.fold_left (fun x y -> x ^ ", " ^ y) first rest

(* 式を文字列にする関数 *)
and e_to_string (e : e) : string = match e with
  | Val (v) -> v_to_string v
  | App (e1, e2) -> "(" ^ e_to_string e1 ^ " " ^ e_to_string e2 ^ ")"
  | Op (name, e) -> "(" ^ name ^ " " ^ e_to_string e ^ ")"
  | With (h, e) ->
    "(with (handler {" ^ h_to_string h ^ "}) handle " ^ e_to_string e ^ ")"

let a_to_string : a -> string = function
  | Return v -> v_to_string v
  | OpCall (name, v, _, _) -> "(" ^ name ^ " " ^ v_to_string v ^ ")"

(* 式を標準出力する *)
let print_e (e : e) : unit =
  print_endline (e_to_string e)

(* 値を標準出力する *)
let print_v (v : v) : unit =
  print_endline (v_to_string v)

let print_a (a : a) : unit =
  print_endline (a_to_string a)
