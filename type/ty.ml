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
  let ctx =
    let rec typeVarsList (t:ty): tv list =
      match t with
      | TypeVariable(uv) -> [uv]
      | RecursiveType(n, b) -> n :: typeVarsList b
      | FunctionType(l, r) -> typeVarsList l @ typeVarsList r
      | RecordType(fs) -> List.concat_map (fun (_,v)->typeVarsList v) fs
      | Union(l, r) -> typeVarsList l @ typeVarsList r
      | Inter(l, r) -> typeVarsList l @ typeVarsList r
      | PrimitiveType _ -> []
    in
    let rec distinct ls =
      ls |> List.fold_left (fun s l ->
        if List.mem l s then s else l::s
      ) [] |> List.rev
    in
    typeVarsList t |> distinct |> (* ユニークな型変数リストを作る *)
    List.mapi (fun i tv -> (* 型変数から変数名へのマップを作る *)
      (* assert(i <= 'z' - 'a', "TODO handle case of not enough chars")*)
      (tv, Printf.sprintf "'%c" (Char.chr (Char.code 'a' + i)))
    )
  in
  let parensIf(str: string) (cnd: bool): string =
    if cnd then "(" ^ str ^ ")" else str
  in
  (* outerPrec: "()" 有無判定用優先順位 *)
  let rec showIn (t:ty) (outerPrec: int): string =
    match t with
    | PrimitiveType(name) -> name
    | TypeVariable(uv) -> List.assoc uv ctx
    | RecursiveType(n, b) -> showIn b 31 ^ " as " ^ List.assoc n ctx
    | FunctionType(l, r) -> parensIf(showIn l 11 ^ " -> " ^ showIn r 10) (outerPrec > 10)
    | RecordType(fs) -> fs |> List.map(fun (k,t) -> k ^ ": " ^ showIn t 0) |>
                        String.concat ", " |> Printf.sprintf "{%s}"
    | Union(l, r) -> parensIf(showIn l 20 ^ " ∨ " ^ showIn r 20) (outerPrec > 20)
    | Inter(l, r) -> parensIf(showIn l 25 ^ " ∧ " ^ showIn r 25) (outerPrec > 25)
  in
  showIn t 0
