(* 式の種類の定義 *)
type expression_desc = Var of string                   (* x *)
                     | Fun of string * expression      (* λx. e *)
                     | App of expression * expression  (* e1 e2 *)
                              
and expression = {desc : expression_desc;  (* 式の内容 *)
                  attr : attribute list}   (* attribute [@x ...] *)

and attribute = (string * payload)     (* 名前と内容のペア *)
and payload = (int * expression) list  (* ステップ番号と簡約前の式 *)

(* コンテキストのフレームの定義 *)
type frame = AppR of expression  (* e [.] *)
           | AppL of expression  (* [.] v *)

(* ステップ番号を格納する変数 *)
let counter : int ref = ref 0

(* attribute を受け取って文字列に変換したものを返す *)
let rec attribute_to_string ((label, payload) : attribute) : string =
  "[@" ^ label ^
  List.fold_left
    (fun x (n, y) -> x ^ "(" ^ string_of_int n ^ ", " ^ to_string y ^ ")")
    " ["
    payload
  ^ "] ]"

(* 式を受け取って文字列に変換したものを返す *)
and to_string (expr : expression) : string =
  let desc_string =
    match expr.desc with
  | Var (x) -> x
  | Fun (x, f) -> "(λ" ^ x ^ ". " ^ to_string f ^ ")"
  | App (e1, e2) -> "(" ^ to_string e1 ^ " " ^ to_string e2 ^ ")" in
  desc_string ^
  List.fold_right (^) (List.map attribute_to_string expr.attr) ""

(* 式を出力する *)
let print (expr : expression) : unit = print_endline (to_string expr)

(* 部分式とコンテキストを受け取って、式全体を返す *)
let rec plug (expr : expression) (ctxt : frame list) : expression =
  match ctxt with
  | [] -> expr
  | AppR (left) :: rest ->
    plug ({desc = App (left, expr); attr = []}) rest
  | AppL (right) :: rest ->
    plug ({desc = App (expr, right); attr = []}) rest

(* ステップ番号をコメントとして出力する *)
let print_counter () : unit =
  print_newline ();
  print_endline ("(* Step " ^ string_of_int !counter ^ " *)")

(* 簡約前後の式とコンテキストを受け取って、そのステップを出力する *)
let memo (redex : expression) (reduct : expression) (context : frame list)
  : unit =
  let marked_redex =
    {redex with attr = ("redex", []) :: redex.attr} in
  let marked_reduct =
    {reduct with attr = ("reduct", []) :: reduct.attr} in
  print_counter ();
  print (plug marked_redex context);
  counter := !counter + 1;
  print_counter ();
  print (plug marked_reduct context)

(* subst e x v で、式 e 内の全ての変数 x を式 v に置換した式を返す *)
let rec subst (e : expression) (x : string) (v : expression) : expression =
  match e.desc with
  | Var (y) -> if x = y then v else e
  | Fun (y, f) ->
    if x = y then e
    else {e with desc = Fun (y, subst f x v)}
  | App (e1, e2) ->
    {e with desc = App (subst e1 x v, subst e2 x v)}

(* 式 expr とその周りのコンテキスト context を受け取ってステップ実行する *)
let rec eval (expr : expression) (context : frame list) : expression =
  match expr.desc with
  | Var (x) -> failwith "error: Unbound variable"
  | Fun (x, f) -> expr
  | App (e1, e2) ->
    let arg_value = eval e2 (AppR e1 :: context) in         (* 引数部分を評価 *)
    let fun_value = eval e1 (AppL arg_value :: context) in  (* 関数部分を評価 *)
    match fun_value.desc with
    | Fun (x, f) ->
      let redex =
        {expr with desc = App (fun_value, arg_value)} in  (* 簡約前の式 *)
      let reduct = {(subst f x arg_value)                 (* 簡約後の式 *)
                    with attr = expr.attr} in
      memo redex reduct context;                        (* ステップ出力 *)
      eval reduct context                            (* 簡約後の式を評価 *)
    | _ -> failwith "error: not a function"

(* 空のコンテキストでステップ実行を始める *)
let start (expr : expression) : expression =
  eval expr []

let var x = {desc = Var x; attr = []}
let func x e = {desc = Fun (x, e); attr = []}
let app e1 e2 = {desc = App (e1, e2); attr = []}
let add e a = {e with attr = a :: e.attr}
let a = "a"
let b = "b"
let c = "c"
let d = "d"
let id x = func x (var x)
let aid = id a
let bid = id b
let cid = id c
let did = id d
let ab = app aid bid
let cd = app cid did
let abcd = app ab cd
let e = abcd
let e0x = add cd ("redex", [])
let e0b = app ab e0x
let e1t = add did ("reduct", [])
let e1a = app ab e1t
let e1x = add ab ("redex", [])
let e1b = app e1x did
let e2t = add bid ("reduct", [])
let e2a = app e2t did
let e2x = add (app bid did) ("redex", [])
let e2b = e2x
let e3t = add did ("reduct", [])
let e3a = e3t

let _ =
  print e;
  print e0b; print e1a; print e1b; print e2a; print e2b; print e3a;
  start e
