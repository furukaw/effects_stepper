open Syntax
open Util
open Memo

(* CPS インタプリタを非関数化して CPS 変換した関数 *)
let rec eval (exp : e) (k : k) (k2 : k2) : a = match exp with
  | Val (v) -> apply_in k v k2
  | App (e1, e2) -> eval e2 (FApp2 (e1, k)) k2
  | Op (name, e) -> eval e (FOp (name, k)) k2
  | With (h, e) ->
    eval e FId (fun a -> apply_handler k h a k2) (* GHandle に変換される関数 *)

(* handle 節内の継続を適用する関数 *)
and apply_in (k : k) (v : v) (k2 : k2) : a = match k with
  | FId -> k2 (Return v)  (* handle 節の外の継続を適用 *)
  | FApp2 (e1, k) -> let v2 = v in
    eval e1 (FApp1 (v2, k)) k2
  | FApp1 (v2, k) -> let v1 = v in
    (match v1 with
     | Fun (x, e) ->
       let reduct = subst e [(x, v2)] in
       eval reduct k k2
     | Cont (k') ->
       apply_in (k' k) v2 k2
     | _ -> failwith "type error")
  | FOp (name, k) -> k2 (OpCall (name, v, k))
  | FCall (k'', h, k') ->
    apply_in k' v (fun a -> apply_handler k'' h a k2) (* GHandle に変換される関数 *)

(* handle 節内の実行結果をハンドラで処理する関数 *)
and apply_handler (k : k) (h : h) (a : a) (k2 : k2) : a = match a with
  | Return v ->
    (match h with {return = (x, e)} ->
       let reduct = subst e [(x, v)] in
       eval reduct k k2)
  | OpCall (name, v, k') ->
    (match search_op name h with
     | None ->
       k2 (OpCall (name, v, FCall (k, h, k'))) (* 外の継続を適用 *)
     | Some (x, y, e) ->
       let cont_value = Cont (fun k -> FCall (k, h, k')) in
       let reduct = subst e [(x, v); (y, cont_value)] in
       eval reduct k k2)

(* 初期継続を渡して実行を始める *)
let stepper (e : e) : a = eval e FId (fun a -> a)  (* GId に変換される関数 *)
