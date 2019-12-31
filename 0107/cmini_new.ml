(* 実行の種類 *)
type mode = All | Next | Prev
let mode = Next
  
(* 式の種類の定義 *)
type expression_desc = Var of string                     (* x *)
                     | Fun of string * expression        (* λx. e *)
                     | App of expression * expression    (* e1 e2 *)

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
    (fun x (n, y) -> x ^ "(" ^ string_of_int n ^ ", " ^ expr_to_string y ^ ")")
    " ["
    payload
  ^ "] ]"

(* 式を受け取って文字列に変換したものを返す *)
(* expr_to_string : expression -> string *)
and expr_to_string (expr : expression) : string =
  let desc_string =
    match expr.desc with
  | Var (x) -> x
  | Fun (x, f) -> "(λ" ^ x ^ ". " ^ expr_to_string f ^ ")"
  | App (e1, e2) -> "(" ^ expr_to_string e1 ^ " " ^ expr_to_string e2 ^ ")" in
  desc_string ^
  List.fold_right (^) (List.map attribute_to_string expr.attr) ""

(* 式を出力する *)
let print (expr : expression) : unit = print_endline (expr_to_string expr)

(* 式を attribute item として出力する *)
let print_as_attribute (expr : expression) : unit =
  if mode != All then
    print_endline ("[@@@stepper.process " ^ expr_to_string expr ^ "]")

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

type mapper = {
  map_attr : mapper -> attribute -> attribute;
  map_attrs : mapper -> attribute list -> attribute list;
  map_expr : mapper -> expression -> expression;
  map_payload : mapper -> payload -> payload;
}

(* 構文木の恒等写像 *)
let rec default_mapper : mapper =
  let rec default_attr mapper (name, args) =
      (name, mapper.map_payload mapper args) in
  let rec default_attrs mapper attrs =
    List.map (mapper.map_attr mapper) attrs in
  let rec default_expr mapper e =
    let new_desc = match e.desc with
      | Var _ -> e.desc
      | Fun (x, f) -> Fun (x, mapper.map_expr mapper f)
      | App (e1, e2) -> App (mapper.map_expr mapper e1,
                             mapper.map_expr mapper e2) in
    {desc = new_desc; attr = mapper.map_attrs mapper e.attr} in
  let rec default_payload mapper pairs =
    List.map (fun (n, redex) -> (n, mapper.map_expr mapper redex)) pairs in
  {map_attr = default_attr;
   map_attrs = default_attrs;
   map_expr = default_expr;
   map_payload = default_payload}

(* 今のステップの [@stepper.reduct ... ] だけを [@t ] にして、あとは消す *)
let rec attrs_reduct_mapper (mapper : mapper)
    (attrs : attribute list) : attribute list =
  match attrs with
  | [] -> []
  | ("stepper.reduct", [(n, redex)]) :: rest ->
    if n = !counter
    then ("t", []) :: attrs_reduct_mapper mapper rest  (* 今簡約した式は短縮 *)
         else attrs_reduct_mapper mapper rest  (* 過去簡約した式は消去 *)
  | _ :: rest -> (* 「簡約後の式」以外の attribute は消去 *)
    attrs_reduct_mapper mapper rest

(* 処理用の簡約後のプログラムを受け取って、表示用の簡約後のプログラムを返す *)
let reduct_mapper : expression -> expression =
  let m = {default_mapper with map_attrs = attrs_reduct_mapper} in
  m.map_expr m

(* [@stepper.redex ] を [@x ] にして、それ以外は消す *)
let rec attrs_redex_mapper (mapper : mapper)
    (attrs : attribute list) : attribute list =
  match attrs with
  | [] -> []
  | (("x", []) as first) :: rest -> [first]
  | first :: rest -> attrs_redex_mapper mapper rest

(* [@stepper.redex ] を [@x ] にして、それ以外の attribute は消す *)
let redex_mapper : expression -> expression =
  let m = {default_mapper with map_attrs = attrs_redex_mapper} in
  m.map_expr m

(* 簡約前後の式とコンテキストを受け取って、そのステップを出力する *)
let memo (redex : expression) (reduct : expression)
    (context : frame list) : unit =
  let marked_redex =                   (* 簡約前の式に attribute 付加 *)
    {redex with attr = ("x", []) :: redex.attr} in
  let marked_reduct =
    {reduct with
     attr = ("stepper.reduct",
             [(!counter + 1,            (* 簡約後の式にステップ番号と、 *)
               redex)])                      (* 簡約前の式の情報を追加 *)
            :: reduct.attr} in
  if mode = Prev                             (* 前ステップ出力のとき、 *)
  then counter := !counter - 1;                (* ステップ番号を１戻す *)
  print_counter ();                         (* 簡約前のステップ番号出力 *)
  print_as_attribute (plug redex context);(* 処理用の簡約前のプログラム *)
  print (redex_mapper
           (plug marked_redex context));  (* 表示用の簡約前のプログラム *)
  counter := !counter + 1;                   (* ステップ番号を１進める *)
  print_counter ();                         (* 簡約前のステップ番号出力 *)
  let latter_program = plug marked_reduct context in
  print_as_attribute (latter_program);    (* 処理用の簡約後のプログラム *)
  print (reduct_mapper latter_program);   (* 表示用の簡約後のプログラム *)
  if mode != All then exit 0      (* 全ステップ実行でなければプロセス終了 *)

(* subst e x v で、式 e 内の全ての変数 x を式 v に置換した式を返す *)
let rec subst (e : expression) (x : string) (v : expression)
  : expression =
  match e.desc with
  | Var (y) -> if x = y then v else e
  | Fun (y, f) ->
    if x = y then e
    else {e with desc = Fun (y, subst f x v)}
  | App (e1, e2) ->
    {e with desc = App (subst e1 x v, subst e2 x v)}

(* 今のステップ番号の [@stepper.reduct ... ] を探してその中の式を返す *)
let rec find_last_reduct (attrs : attribute list) : expression =
  match attrs with
  | [] -> raise Not_found
  | ("stepper.reduct", [(n, redex)]) :: _
    when n = !counter -> redex
  | _ :: rest -> find_last_reduct rest

(* 式とその周りのコンテキストを受け取ってステップ実行する *)
let rec eval (expr : expression) (context : frame list)
  : expression =
  if mode = Prev
  then begin try
      let redex = find_last_reduct expr.attr in
      memo redex expr context;
    with Not_found -> ()
  end;
  match expr.desc with
  | Var (x) -> failwith "error: Unbound variable"
  | Fun (x, f) -> expr
  | App (e1, e2) ->
    let arg_value = eval e2 (AppR e1 :: context) in
    let fun_value = eval e1 (AppL arg_value :: context) in
    match fun_value.desc with              (* 以下、次ステップの簡約 *)
    | Fun (x, f) ->
      let redex = {expr with desc = App (fun_value, arg_value)} in
      let reduct = {(subst f x arg_value)
                    with attr = expr.attr} in
      memo redex reduct context;
      eval reduct context
    | _ -> failwith "error: not a function"

(* 空のコンテキストでステップ実行を始める *)
let start (expr : expression) : expression =
  eval expr []

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
let p0b = e
let s0x = add cd ("x", [])
let s0b = app ab s0x
let p1t = add did ("stepper.reduct", [(1, cd)])
let p1a = app ab p1t
let s1t = add did ("t", [])
let s1a = app ab s1t
let p1b = app ab p1t
let s1x = add ab ("x", [])
let s1b = app s1x did
let p2t = add bid ("stepper.reduct", [(2, ab)])
let p2a = app p2t p1t
let s2t = add bid ("t", [])
let s2a = app s2t did
let p2b = app p2t p1t
let s2x = add (app bid did) ("x", [])
let s2b = s2x
let p3t = add did ("stepper.reduct", [(3, p2b)])
let p3a = p3t
let s3t = add did ("t", [])
let s3a = s3t

let _ =
  print_as_attribute p0b;
  print s0b;
  print_as_attribute p1a;
  print s1a;
  (* counter := 0;
   * ignore(start e); *)
  (* counter := 1;
   * ignore (start p1b); *)
  print_as_attribute p1b;
  print s1b;
  print_as_attribute p2a;
  print s2a;
  counter := 1;
  ignore(start p1a);
  (* counter := 2;
   * ignore (start p2b); *)
  print_as_attribute p2b;
  print s2b;
  print_as_attribute p3a;
  print s3a;
  (* counter := 2;
   * ignore(start p2a); *)
  counter := 0;
  start e
