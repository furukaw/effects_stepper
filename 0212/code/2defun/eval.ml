open Syntax
open Util
open Memo

(* CPS インタプリタを非関数化した関数 *)
let rec eval (exp : e) (k : k) : a = match exp with
  | Val (v) -> apply_in k v  (* 継続適用関数に継続と値を渡す *)
  | App (e1, e2) -> eval e2 (FApp2 (e1, k))
  | Op (name, e) -> eval e (FOp (name, k))
  | With (h, e) -> let a = eval e FId in  (* 空の継続を渡す *)
    apply_handler k h a  (* handle 節内の実行結果をハンドラで処理 *)

(* handle 節内の継続を適用する関数 *)
and apply_in (k : k) (v : v) : a = match k with
  | FId -> Return v  (* 空の継続、そのまま値を返す *)
  | FApp2 (e1, k) -> let v2 = v in eval e1 (FApp1 (v2, k))
  | FApp1 (v2, k) -> let v1 = v in
    (match v1 with
      | Fun (x, e) ->
        let reduct = subst e [(x, v2)] in
        eval reduct k
      | Cont (cont_value) ->
        (cont_value k) v2
      | _ -> failwith "type error")
  | FOp (name, k) ->
    OpCall (name, v, (fun v -> apply_in k v))  (* Op 呼び出しの情報を返す *)

(* handle 節内の実行結果をハンドラで処理する関数 *)
and apply_handler (k : k) (h : h) (a : a) : a = match a with
  | Return v ->
    (match h with {return = (x, e)} ->
      let reduct = subst e [(x, v)] in
      eval reduct k)
  | OpCall (name, v, m) ->
    (match search_op name h with
      | None ->
        OpCall (name, v, (fun v ->
          let a' = m v in
          apply_handler k h a'))
      | Some (x, y, e) ->
        let cont_value =
          Cont (fun k'' -> fun v ->
            let a' = m v in
            apply_handler k'' h a') in
        let reduct = subst e [(x, v); (y, cont_value)] in
        eval reduct k)

(* 初期継続を渡して実行を始める *)
let interpreter (e : e) : a = eval e FId
