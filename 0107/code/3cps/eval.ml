open Syntax
open Util
open Memo

(* CPS インタプリタを非関数化して CPS 変換した関数 *)
let rec eval (exp : e) (k : k) (k2 : k2) : a = match exp with
  | Val (v) -> apply_in k v k2
  | App (e1, e2) -> eval e2 (FApp2 (e1, k)) k2
  | Op (name, e) -> eval e (FOp (name, k)) k2
  | With (h, e) ->
    eval e FId (fun a -> apply_handler k h a k2)  (* GHandle に変換される *)

(* handle 節内の継続を適用する関数 *)
and apply_in (k : k) (v : v) (k2 : k2) : a = match k with
  | FId -> k2 (Return v)
  | FApp2 (e1, k) -> let v2 = v in
    eval e1 (FApp1 (v2, k)) k2
  | FApp1 (v2, k) -> let v1 = v in
    (match v1 with
     | Fun (x, e) ->
       let reduct = subst e [(x, v2)] in
       eval reduct k k2
     | Cont (cont_value) ->
       (cont_value k) v2 k2
     | _ -> failwith "type error")
  | FOp (name, k) ->
    k2 (OpCall (name, v, (fun v -> fun k2' -> apply_in k v k2')))

(* handle 節内の実行結果をハンドラで処理する関数 *)
and apply_handler (k : k) (h : h) (a : a) (k2 : k2) : a = match a with
  | Return v ->
    (match h with {return = (x, e)} ->
       let reduct = subst e [(x, v)] in
       eval reduct k k2)
  | OpCall (name, v, va) ->
    (match search_op name h with
     | None ->
       k2 (OpCall (name, v, (fun v -> fun k2' ->
           va v (fun a' -> apply_handler k h a' k2')))) (* GHandle に変換される *)
     | Some (x, y, e) ->
       let cont_value =
         Cont (fun k'' -> fun v -> fun k2 ->
             va v (fun a' -> apply_handler k'' h a' k2)) in  (* GHandle に変換 *)
       let reduct = subst e [(x, v); (y, cont_value)] in
       eval reduct k k2)

(* 初期継続を渡して実行を始める *)
let interpreter (e : e) : a = eval e FId (fun a -> a)  (* GId に変換される *)
