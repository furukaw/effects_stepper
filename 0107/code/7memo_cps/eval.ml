open Syntax
open Util
open Memo

(* CPS インタプリタ *)
let rec eval (exp : e) ((k, c) : k * c) (c2 : c2) : a = match exp with
  | Val (v) -> k v  (* 継続に値を渡す *)
  | App (e1, e2) ->
    eval e2 ((fun v2 ->  (* FApp2 に変換される関数 *)
        eval e1 ((fun v1 -> match v1 with  (* FApp1 に変換される関数 *)
            | Fun (x, e) ->
              let redex = App (Val v1, Val v2) in  (* (fun x -> e) v2 *)
              let reduct = subst e [(x, v2)] in  (* e[v2/x] *)
              memo redex reduct (c, c2);
              eval reduct (k, c) c2
            | Cont (x, cont_value, c') ->
              let redex = App (Val v1, Val v2) in               (* k' v2 *)
              let reduct = plug_in_handle (Val v2) c'  in  (* k'[v2] *)
              memo redex reduct (c, c2);
              (cont_value (k, c)) v2  (* 現在の継続と継続値が保持するメタ継続を合成して値を渡す *)
            | _ -> failwith "type error"
          ), FApp1 (v2, c)) c2
      ), FApp2 (e1, c)) c2
  | Op (name, e) ->
    eval e ((fun v -> OpCall (name, v, (k, c))), FOp (name, c)) c2  (* FOp に変換される関数 *)
  | With (h, e) ->
    let a = eval e ((fun v -> Return v), FId) (GHandle (c, h, c2)) in  (* FId に変換される関数、空の継続 *)
    apply_handler (k, c) h a c2  (* handle 節内の実行結果をハンドラで処理 *)

(* handle 節内の実行結果をハンドラで処理する関数 *)
and apply_handler ((k, c) : k * c) (h : h) (a : a) (c2 : c2) : a = match a with
  | Return v ->                         (* handle 節内が値 v を返したとき *)
    (match h with {return = (x, e)} ->  (* handler {return x -> e, ...} として*)
       let redex = With (h, Val v) in (* with handler{return x -> e} handle v *)
       let reduct = subst e [(x, v)] in (* e[v/x] に簡約される *)
       memo redex reduct (c, c2);
       eval reduct (k, c) c2)                   (* e[v/x] を実行 *)
  | OpCall (name, v, (k', c')) ->        (* オペレーション呼び出しがあったとき *)
    (match search_op name h with
     | None ->                     (* ハンドラで定義されていない場合、 *)
       OpCall (name, v, ((fun v ->  (* OpCall の継続の後に現在の継続を合成 *)
           let a' = k' v in
           apply_handler (k, c) h a' c2), FCall (c, h, c')))  (* FCall に変換される関数 *)
     | Some (x, y, e) ->           (* ハンドラで定義されている場合、 *)
       let redex = (* with handler {name(x; y) -> e} handle k'[(name v)] *)
         With (h, plug_in_handle (Op (name, Val v)) c') in
       let new_var = gen_var_name () in
       let cont_value =
         Cont (new_var,
               (fun (k'', c'') -> fun v -> (* 適用時にその後の継続を受け取って合成 *)
                  let a' = k' v in
                  apply_handler (k'', c'') h a' c2),
               FCall (FId, h, c')) in  (* FCall に変換される関数 *)
       let reduct = subst e [(x, v); (y, cont_value)] in
       memo redex reduct(c, c2);
       eval reduct (k, c) c2)

(* 初期継続を渡して実行を始める *)
let stepper (e : e) : a = eval e ((fun v -> Return v), FId) GId (* FIdに変換される関数 *)
