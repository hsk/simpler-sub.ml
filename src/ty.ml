(* Types *)
type tv = string * int
type ty =
 | Union of ty * ty
 | Inter of ty * ty
 | FunctionType of ty * ty
 | RecordType of (string * ty) list
 | RecursiveType of tv * ty
 | PrimitiveType of string
 | TypeVariable of tv

let show(t:ty): string =
  let rec distinct ls =
    ls |> List.fold_left (fun s l ->
      if List.mem l s then s else l::s
    ) [] |> List.rev
  in
  let rec typeVarsList (t:ty): tv list =
    let children(t:ty): ty list = match t with
      | FunctionType(l, r) -> [l;r]
      | RecordType(fs) -> List.map snd fs
      | Union(l, r) -> [l; r]
      | Inter(l, r) -> [l; r]
      | RecursiveType(n, b) -> [b]
      | _ -> []
    in
    match t with
    | TypeVariable(uv) -> [uv]
    | RecursiveType(n, b) -> n :: typeVarsList b
    | _ -> children t |> List.concat_map typeVarsList
  in
  let rec showIn (t:ty) (ctx: (tv * string) list) (outerPrec: int): string =
    let parensIf(str: string) (cnd: bool): string =
      if cnd then "(" ^ str ^ ")" else str
    in
    match t with
    | PrimitiveType(name) -> name
    | TypeVariable(uv) -> List.assoc uv ctx
    | RecursiveType(n, b) -> showIn b ctx 31 ^ " as " ^ List.assoc n ctx
    | FunctionType(l, r) -> parensIf(showIn l ctx 11 ^ " -> " ^ showIn r ctx 10) (outerPrec > 10)
    | RecordType(fs) ->
      fs |> List.map(fun (k,t) -> k ^ ": " ^ showIn t ctx 0)|>
      String.concat ", " |> Printf.sprintf "{%s}"
    | Union(l, r) -> parensIf(showIn l ctx 20 ^ " ∨ " ^ showIn r ctx 20) (outerPrec > 20)
    | Inter(l, r) -> parensIf(showIn l ctx 25 ^ " ∧ " ^ showIn r ctx 25) (outerPrec > 25)
  in
  let vars = typeVarsList t |> distinct in (* リスト内の値をユニークにする *)
  let ctx = vars |> List.mapi (fun idx tv ->
      (* assert(idx <= 'z' - 'a', "TODO handle case of not enough chars")*)
      let nme = (Char.code 'a' + idx)|> Char.chr |> Printf.sprintf "'%c" in
      (tv, nme))
  in
  showIn t ctx 0
