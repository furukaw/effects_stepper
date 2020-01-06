open Syntax
open Util
open Memo

(* CPS インタプリタ *)
let rec eval (exp : e) (k : k) : a = match exp with
  | Val (v) -> apply_in k v  (* 継続に値を渡す *)
  | App (e1, e2) ->
    eval e2 (FApp2 (e1, k))
  | Op (name, e) ->
    eval e (FOp (name, k))  (* FOp に変換される関数 *)
  | With (h, e) ->
    let a = eval e FId in  (* FId に変換される関数、空の継続 *)
    apply_handler k h a  (* handle 節内の実行結果をハンドラで処理 *)

and apply_in (k : k) (v : v) : a = match k with
  | FId -> Return v
  | FApp2 (e1, k) -> let v2 = v in
    eval e1 (FApp1 (v2, k))
  | FApp1 (v2, k) -> let v1 = v in
    (match v1 with
     | Fun (x, e) ->
       let reduct = subst e [(x, v2)] in  (* e[v2/x] *)
       eval reduct k
     | Cont (cont_value) ->
       (cont_value k) v2
     | _ -> failwith "type error")
  | FOp (name, k) -> OpCall (name, v, (fun v -> apply_in k v))    

(* handle 節内の実行結果をハンドラで処理する関数 *)
and apply_handler (k : k) (h : h) (a : a) : a = match a with
  | Return v ->                         (* handle 節内が値 v を返したとき *)
    (match h with {return = (x, e)} ->  (* handler {return x -> e, ...} として*)
       let reduct = subst e [(x, v)] in (* e[v/x] に簡約される *)
       eval reduct k)                   (* e[v/x] を実行 *)
  | OpCall (name, v, va) ->        (* オペレーション呼び出しがあったとき *)
    (match search_op name h with
     | None ->                     (* ハンドラで定義されていない場合、 *)
       OpCall (name, v, (fun v ->  (* OpCall の継続の後に現在の継続を合成 *)
           let a' = va v in
           apply_handler k h a'))  (* FCall に変換される関数 *)
     | Some (x, y, e) ->           (* ハンドラで定義されている場合、 *)
       let cont_value =
         Cont (fun k'' -> fun v -> (* 適用時にその後の継続を受け取って合成 *)
             let a' = va v in
             apply_handler k'' h a') in  (* FCall に変換される関数 *)
       let reduct = subst e [(x, v); (y, cont_value)] in
       eval reduct k)

(* 初期継続を渡して実行を始める *)
let interpreter (e : e) : a = eval e FId (* FIdに変換される関数 *)
