(* 式の種類の定義 *)
type expr_desc = Var of string         (* x *)
                     | Fun of string * expr  (* λx. e *)
                     | App of expr * expr    (* e1 e2 *)
                              
and expr = {desc : expr_desc;
            attr : (string * expr list) list}

(* コンテキストのフレームの定義 *)
type frame = AppR of expr  (* e [.] *)
           | AppL of expr  (* [.] v *)

(* コンテキストを格納する変数 *)
let context: frame list ref = ref []

(* ステップ番号を格納する変数 *)
let counter = ref 0

(* attribute を受け取って文字列に変換したものを返す *)
(* attribute_to_string : string * expr list -> string *)
let rec attribute_to_string (label, exprs) =
  "[@" ^ label ^ List.fold_left (fun x y -> x ^ " ;;" ^ to_string y) "" exprs ^ "]"

(* 式を受け取って文字列に変換したものを返す *)
(* to_string : expr -> string *)
and to_string expr =
  let desc_string =
    match expr.desc with
  | Var (x) -> x
  | Fun (x, f) -> "(λ" ^ x ^ ". " ^ to_string f ^ ")"
  | App (e1, e2) -> "(" ^ to_string e1 ^ " " ^ to_string e2 ^ ")" in
  desc_string ^
  List.fold_right (^) (List.map attribute_to_string expr.attr) ""

(* 式を出力する *)
(* print : expr -> unit *)
let print expr = print_endline (to_string expr)

(* 部分式とコンテキストを受け取って、式全体を構築する *)
(* plug : expr -> frame list -> expr *)
let rec plug expr ctxt = match ctxt with
  | [] -> expr
  | AppR (left) :: rest ->
    plug ({desc = App (left, expr); attr = []}) rest
  | AppL (right) :: rest ->
    plug ({desc = App (expr, right); attr = []}) rest

(* ステップ番号を出力する *)
(* print_counter : unit -> unit *)
let print_counter () =
  print_newline ();
  print_endline ("(* Step " ^ string_of_int !counter ^ " *)")
    
(* 簡約前後の式を受け取って、プログラム全体を出力する *)
(* memo : expr -> expr -> unit *)
let memo redex reduct =
  let current_context = !context in
  print_counter ();
  print (plug redex current_context);
  counter := !counter + 1;
  print_counter ();
  print (plug reduct current_context)

(* subst e x v で、式 e 内の全ての変数 x を式 v に置換 *)
(* subst : expr -> string -> expr -> expr *)
let rec subst e x v = match e.desc with
  | Var (y) -> if x = y then v else e
  | Fun (y, f) ->
    if x = y then e
    else {e with desc = Fun (y, subst f x v)}
  | App (e1, e2) ->
    {e with desc = App (subst e1 x v, subst e2 x v)}

(* ステップ実行インタプリタ *)
(* eval : expr -> expr *)
let rec eval expr =
  match expr.desc with
  | Var (x) -> failwith "error: Unbound variable"
  | Fun (x, f) -> expr
  | App (e1, e2) ->
    context := (AppR e1) :: !context;
    let arg_value = eval e2 in
    context := List.tl !context;
    context := (AppL arg_value) :: !context;
    let fun_value = eval e1 in
    context := List.tl !context;
    match fun_value.desc with
    | Fun (x, f) ->
      let reduct = subst f x arg_value in
      let marked_redex =
        {desc = (App (fun_value, arg_value));
         attr = ("redex", []) :: expr.attr} in
      let marked_reduct =
        {reduct with attr = ("reduct", []) :: expr.attr} in
      memo marked_redex marked_reduct;
      eval reduct
    | _ -> failwith "error: not a function"

(* 初期化してステップ実行を始める *)
(* start : expr -> expr *)
let start expr =
  context := [];
  counter := 0;
  eval expr

let var x = {desc = Var x; attr = []}
let func x e = {desc = Fun (x, e); attr = []}
let app e1 e2 = {desc = App (e1, e2); attr = []}
let x = "x"
let xid = func "x" (var "x")
let yz = func "y" (var "z")
let xidyz = app xid yz
let exidyz = eval xidyz
(* let xxx = (func x (app (var x) (var x)))
 * let omega = app xxx xxx
 * let eomega = eval omega *)
let yid = func "y" (var "y")
let zid = func "z" (var "z")
let xyx = func "x" (func "y" (var "x"))
let ex = app (app xyx yid) zid
let eex = start ex

