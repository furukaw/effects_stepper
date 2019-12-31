(* 実行の種類 *)
type mode = All | Next | Prev
let mode = Prev
  
(* 式の種類の定義 *)
type expression_desc = Var of string         (* x *)
                     | Fun of string * expr  (* λx. e *)
                     | App of expr * expr    (* e1 e2 *)
                              
and expr = {desc : expression_desc;
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
  "[@" ^ label ^ List.fold_left (fun x y -> x ^ " ;;" ^ to_string y) "" exprs ^ " ]"

(* 式を受け取って文字列に変換したものを返す *)
(* to_string : expression -> string *)
and to_string expr =
  let desc_string =
    match expr.desc with
  | Var (x) -> x
  | Fun (x, f) -> "(λ" ^ x ^ ". " ^ to_string f ^ ")"
  | App (e1, e2) -> "(" ^ to_string e1 ^ " " ^ to_string e2 ^ ")" in
  desc_string ^
  List.fold_right (^) (List.map attribute_to_string expr.attr) ""

(* 式を出力する *)
(* print : expression -> unit *)
let print expr = print_endline (to_string expr)

(* 部分式を受け取って、式全体を返す *)
(* plug : expression -> frame list -> expression *)
let rec plug expr ctxt = match ctxt with
  | [] -> expr
  | AppR (left) :: rest ->
    plug ({desc = App (left, expr); attr = []}) rest
  | AppL (right) :: rest ->
    plug ({desc = App (expr, right); attr = []}) rest

(* ステップ番号を出力する *)
(* print_counter : unit -> unit *)
let print_counter () =
  print_endline ("\n(* Step " ^ string_of_int !counter ^ " *)")
    
(* 簡約前後の式を受け取って、プログラム全体を出力する *)
(* memo : expression -> expression -> unit *)
let memo redex reduct =
  let current_context = !context in
  if mode = Prev then counter := !counter - 1;
  print_counter ();
  print (plug redex current_context);
  counter := !counter + 1;
  print_counter ();
  print (plug reduct current_context);
  if mode != All then exit 0

(* subst e x v で、式 e 内の全ての変数 x を式 v に置換 *)
(* subst : expression -> string -> expression -> expression *)
let rec subst e x v = match e.desc with
  | Var (y) -> if x = y then v else e
  | Fun (y, f) ->
    if x = y then e
    else {e with desc = Fun (y, subst f x v)}
  | App (e1, e2) ->
    {e with desc = App (subst e1 x v, subst e2 x v)}

let rec find_last_reduct attrs = match attrs with
  | [] -> raise Not_found
  | ("reduct", {desc = Var n} :: redex :: []) :: _
    when int_of_string n = !counter -> redex
  | _ :: rest -> find_last_reduct rest

let wrap_expr desc = {desc = desc; attr = []}

(* ステップ実行インタプリタ *)
(* eval : expression -> expression *)
let rec eval expr =
  if mode = Prev
  then begin try
      let marked_redex = find_last_reduct expr.attr in
      memo marked_redex expr;
    with Not_found -> ()
  end;
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
      let counter_expr = {desc = Var (string_of_int (!counter + 1));
                          attr = []} in  (* ステップ番号を表す式を定義 *)
      let marked_redex =
        {desc = (App (fun_value, arg_value));
         attr = ("redex", [counter_expr])  (* ステップ番号を表す式を追加 *)
                :: expr.attr} in
      let marked_reduct =
        {reduct with
         attr =
           ("reduct",
            [counter_expr;   (* ステップ番号を表す式 *)
             marked_redex])  (* 簡約前の式 *)
           :: expr.attr} in
      memo marked_redex marked_reduct;
      eval marked_reduct
    | _ -> failwith "error: not a function"

let start expr =
  context := [];
  eval expr

(* テスト *)

let var x = {desc = Var x; attr = []}
let func x e = {desc = Fun (x, e); attr = []}
let app e1 e2 = {desc = App (e1, e2); attr = []}
let add expr attr = {expr with attr = attr :: expr.attr}
(* ((la. a) (lb. b)) ((lc. c) (ld. d)) *)
let id x = func x (var x)
let aid = id "a"
let bid = id "b"
let cid = id "c"
let did = id "d"
let ab = app aid bid
let cd = app cid did
let abcd = app ab cd
let e = abcd
let e0x = add cd ("redex", [var "1"])
let e0 = app ab e0x
let e1t = add did ("reduct", [var "1"; e0x])
let e1a = app ab e1t
let e1x = add ab ("redex", [var "2"])
let e1b = app e1x e1t
let e2t = add bid ("reduct", [var "2"; e1x])
let e2a = app e2t e1t
let e2x = add e2a ("redex", [var "3"])
let e2b = e2x
let e3 = add did ("reduct", [var "3"; e2x])
    
let () =
  print e0; print e1a; print e1b; print e2a; print e2b; print e3;
  counter := 1;
  ignore(start e1b)
