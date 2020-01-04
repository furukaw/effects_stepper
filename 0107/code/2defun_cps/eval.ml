open Syntax
open Util
open Memo

(* CPS インタプリタを非関数化した関数 *)
let rec eval (exp : e) (k : k) : a = match exp with
  | Val (v) -> apply_in k v  (* 継続適用関数に継続と値を渡す *)
  | App (e1, e2) -> eval e2 (FApp2 (e1, k))
  | Op (name, e) -> eval e (FOp (name, k))
  | With (h, e) ->
    let a = eval e FId in  (* 空の継続を渡す *)
    apply_handler k h a  (* handle 節内の実行結果をハンドラで処理 *)

(* handle 節内の継続を適用する関数 *)
and apply_in (k : k) (v : v) : a = match k with
  | FId -> Return v  (* 空の継続、そのまま値を返す *)
  | FApp2 (e1, k) -> let v2 = v in
    eval e1 (FApp1 (v2, k))
  | FApp1 (v2, k) -> let v1 = v in
    (match v1 with
     | Fun (x, e) ->
       let reduct = subst e [(x, v2)] in
       eval reduct k
     | Cont (k') ->
       apply_in (k' k) v2
     | _ -> failwith "type error")
  | FOp (name, k) -> OpCall (name, v, k)  (* この handle 節の実行結果は OpCall *)
  | FCall (k'', h, k') ->  (* k''[with h handle k'[v]] *)
    let a = apply_in k' v in  (* handle 節までの継続を適用 *)
    apply_handler k'' h a  (* a をハンドラ h で処理して、その後 k'' を適用 *)

(* handle 節内の実行結果をハンドラで処理する関数 *)
and apply_handler (k : k) (h : h) (a : a) : a = match a with
  | Return v ->
    (match h with {return = (x, e)} ->
       let reduct = subst e [(x, v)] in
       eval reduct k)
  | OpCall (name, v, k') ->
    (match search_op name h with
     | None -> OpCall (name, v, FCall (k, h, k'))
     | Some (x, y, e) ->
       let cont_value = Cont (fun k -> FCall (k, h, k')) in
       let reduct = subst e [(x, v); (y, cont_value)] in
       eval reduct k)

(* 初期継続を渡して実行を始める *)
let stepper (e : e) : a = eval e FId
