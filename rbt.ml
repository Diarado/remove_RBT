open Dictionary

module Make =
functor
  (K : KeySig)
  (V : ValueSig)
  ->
  struct
    module Key = K
    module Value = V

    type key = K.t
    type value = V.t

    (* AF: The dictionary is represented by a red-black tree where each node is
       a Leaf or a Node with a color, a left subtree, a key, a value, and a
       right subtree. RI: k value with a defined comparator must satisfy BST
       invariant & red-black invariants. *)

    type color =
      | Red
      | Blk
      | BB

    type t =
      | Leaf
      | LL
      | Node of color * t * key * value * t

    let debug = false

    let rep_ok d =
      if debug then
        let rec check_bst = function
          | Leaf -> true
          | LL -> true
          | Node (_, l, k, _, r) -> (
              check_bst l && check_bst r
              && (match l with
                 | Leaf -> true
                 | LL -> true
                 | Node (_, _, k', _, _) -> K.compare k' k = LT)
              &&
              match r with
              | Leaf -> true
              | LL -> true
              | Node (_, _, k', _, _) -> K.compare k' k = GT)
        in
        let cnt = ref 0 in
        let rec check_color = function
          | Leaf -> Blk
          | LL -> Blk
          | Node (c, l, _, _, r) ->
              if c = Red && (check_color l = Red || check_color r = Red) then
                failwith "RI: root is blk & no red node has red child"
              else if !cnt = 0 && c = Blk then (
                cnt := !cnt + 1;
                Blk (*check the root is blk*))
              else (
                cnt := !cnt + 1;
                Blk)
        in
        let rec check_blk_height d =
          (* the black height of the whole tree *)
          let rec cnt_blks = function
            | Leaf -> 1 (* Leaf is always blk *)
            | LL -> 1
            | Node (c, l, _, _, r) ->
                let lbh = cnt_blks l in
                let rbh = cnt_blks r in
                if lbh <> rbh then failwith "RI: black height is constant"
                else if c = Blk then lbh + 1
                else lbh
          in
          cnt_blks d <> 0
        in
        if check_bst d && check_color d = Blk && check_blk_height d then d
        else failwith "RI: BST"
      else d
      [@@coverage off]

    let empty = Leaf
    let is_empty d = d = Leaf

    let rec size = function
      | Node (_, l, _, _, r) -> 1 + size l + size r
      | _ -> 0

    let balance2 = function
      | Blk, Node (Red, Node (Red, a, x, x', b), y, y', c), z, z', d
      | Blk, Node (Red, a, x, x', Node (Red, b, y, y', c)), z, z', d
      | Blk, a, x, x', Node (Red, Node (Red, b, y, y', c), z, z', d)
      | Blk, a, x, x', Node (Red, b, y, y', Node (Red, c, z, z', d)) ->
          Node (Red, Node (Blk, a, x, x', b), y, y', Node (Blk, c, z, z', d))
      | BB, a, x, x', Node (Red, Node (Red, b, y, y', c), z, z', d)
      | BB, Node (Red, a, x, x', Node (Red, b, y, y', c)), z, z', d ->
          Node (Blk, Node (Blk, a, x, x', b), y, y', Node (Blk, c, z, z', d))
      | Blk, l, k, v, r -> Node (Blk, l, k, v, r)
      | c, l, k, v, r -> Node (c, l, k, v, r)

    let rec insert_aux k' v' = function
      | Node (c, l, k, v, r) ->
          if K.compare k' k = LT then
            rep_ok (balance2 (c, insert_aux k' v' l, k, v, r))
          else if K.compare k' k = GT then
            rep_ok (balance2 (c, l, k, v, insert_aux k' v' r))
          else rep_ok (Node (c, l, k, v', r))
      | _ -> Node (Red, Leaf, k', v', Leaf)

    let insert k v d =
      match insert_aux k v d with
      | Node (_, l, k, v, r) -> rep_ok (Node (Blk, l, k, v, r))
      | _ -> failwith "insert not valid"

    (* Remove helper *)
    let redden = function
      | Node (Blk, Node (Blk, a, x, x', b), y, y', Node (Blk, c, z, z', d)) ->
          Node (Red, Node (Blk, a, x, x', b), y, y', Node (Blk, c, z, z', d))
      | t -> t

    (* Remove helper *)
    let rotate = function
      | Red, Node (BB, a, x, x', b), y, y', Node (Blk, c, z, z', d) ->
          balance2 (Blk, Node (Red, Node (Blk, a, x, x', b), y, y', c), z, z', d)
          (*1*)
      | Red, LL, y, y', Node (Blk, c, z, z', d) ->
          balance2 (Blk, Node (Red, Leaf, y, y', c), z, z', d) (*2*)
      | Red, Node (Blk, a, x, x', b), y, y', Node (BB, c, z, z', d) ->
          balance2 (Blk, a, x, x', Node (Red, b, y, y', Node (Blk, c, z, z', d)))
          (*3*)
      | Red, Node (Blk, a, x, x', b), y, y', LL ->
          balance2 (Blk, a, x, x', Node (Red, b, y, y', Leaf)) (*4*)
      | Blk, Node (BB, a, x, x', b), y, y', Node (Blk, c, z, z', d) ->
          balance2 (BB, Node (Red, Node (Blk, a, x, x', b), y, y', c), z, z', d)
          (*5*)
      | Blk, LL, y, y', Node (Blk, c, z, z', d) ->
          balance2 (BB, Node (Red, Leaf, y, y', c), z, z', d) (*6*)
      | Blk, Node (Blk, a, x, x', b), y, y', Node (BB, c, z, z', d) ->
          balance2 (BB, a, x, x', Node (Red, b, y, y', Node (Blk, c, z, z', d)))
          (*7*)
      | Blk, Node (Blk, a, x, x', b), y, y', LL ->
          balance2 (BB, a, x, x', Node (Red, b, y, y', Leaf)) (*8*)
      | ( Blk,
          Node (BB, a, w, w', b),
          x,
          x',
          Node (Red, Node (Blk, c, y, y', d), z, z', e) ) ->
          Node
            ( Blk,
              balance2
                (Blk, Node (Red, Node (Blk, a, w, w', b), x, x', c), y, y', d),
              z,
              z',
              e )
          (*9*)
      | Blk, LL, x, x', Node (Red, Node (Blk, c, y, y', d), z, z', e) ->
          Node
            (Blk, balance2 (Blk, Node (Red, Leaf, x, x', c), y, y', d), z, z', e)
          (*10*)
      | ( Blk,
          Node (Red, a, w, w', Node (Blk, b, x, x', c)),
          y,
          y',
          Node (BB, d, z, z', e) ) ->
          Node
            ( Blk,
              a,
              w,
              w',
              balance2
                (Blk, b, x, x', Node (Red, c, y, y', Node (Blk, d, z, z', e)))
            )
          (*11*)
      | Blk, Node (Red, a, w, w', Node (Blk, b, x, x', c)), y, y', LL ->
          Node
            (Blk, a, w, w', balance2 (Blk, b, x, x', Node (Red, c, y, y', Leaf)))
          (*12*)
      | c, l, k, v, r -> Node (c, l, k, v, r)

    (* Remove Helper*)
    let rec min_del = function
      | Node (Red, Leaf, x, x', Leaf) -> (x, x', Leaf)
      | Node (Blk, Leaf, x, x', Leaf) -> (x, x', LL)
      | Node (Blk, Leaf, x, x', Node (Red, Leaf, y, y', Leaf)) ->
          (x, x', Node (Blk, Leaf, y, y', Leaf))
      | Node (c, a, x, x', b) ->
          let k, v, a' = min_del a in
          (k, v, rotate (c, a', x, x', b))
      | _ -> raise (Invalid_argument "min_del: Empty tree")

    let rec remove k d =
      let rec del = function
        | Node (Red, Leaf, y, y', Leaf) as t ->
            if K.compare k y = EQ then Leaf else t
        | Node (Blk, Leaf, y, y', Leaf) as t ->
            if K.compare k y = EQ then LL else t
        | Node (Blk, Node (Red, Leaf, y, y', Leaf), z, z', Leaf) as t ->
            if K.compare k z = LT then
              Node (Blk, del (Node (Red, Leaf, y, y', Leaf)), z, z', Leaf)
            else if K.compare k z = EQ then Node (Blk, Leaf, y, y', Leaf)
            else t
        | Node (c, a, y, y', b) -> (
            if K.compare k y = LT then rotate (c, del a, y, y', b)
            else if K.compare k y = GT then rotate (c, a, y, y', del b)
            else
              try
                let y', y'', b' = min_del b in
                rotate (c, a, y', y'', b')
              with Invalid_argument s -> Leaf)
        | _ -> Leaf
      in
      rep_ok (del (redden d))

    let rec find k = function
      | Node (_, l, kk, vv, r) ->
          if K.compare k kk = LT then find k l
          else if K.compare k kk = GT then find k r
          else Some vv
      | _ -> None

    let rec member k = function
      | Node (_, l, kk, vv, r) ->
          if K.compare k kk = LT then member k l
          else if K.compare k kk = GT then member k r
          else true
      | _ -> false

    let rec to_list = function
      | Node (_, l, k, v, r) -> to_list l @ [ (k, v) ] @ to_list r
      | _ -> []

    let fold f acc d =
      let rec fold_aux acc = function
        | Node (_, l, k, v, r) -> fold_aux (f k v (fold_aux acc l)) r
        | _ -> acc
      in
      fold_aux acc d

    let to_string d =
      let rec aux = function
        | Node (_, l, k, v, r) ->
            let str_of_pair (k, v) = K.to_string k ^ ": " ^ V.to_string v in
            aux l ^ str_of_pair (k, v) ^ "; " ^ aux r
        | _ -> ""
      in
      let raw = aux d in
      let f = String.sub raw 0 (String.length raw - 2) in
      "[" ^ f ^ "]"
  end
