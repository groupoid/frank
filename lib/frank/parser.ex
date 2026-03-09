defmodule Frank.Parser do
  alias Frank.AST

  def parse(tokens) do
    parse_module(tokens)
  end

  def parse_expression(tokens) do
    parse_expr(tokens)
  end

  def parse_declaration(tokens) do
    parse_decl(tokens)
  end

  defp parse_module(tokens) do
    # Skip any leading virtual tokens
    tokens = Enum.drop_while(tokens, fn t -> elem(t, 0) == :v_left_brace end)

    case tokens do
      [{:module, _, _} | rest] ->
        case parse_module_name(rest) do
          {:ok, name, [{:where, _, _} | rest2]} ->
            case parse_decls(rest2, []) do
              {:ok, decls, remaining} ->
                {:ok, %AST.Module{name: name, declarations: decls}, remaining}
            end

          _ ->
            {:error, {:invalid_module_header, Enum.take(rest, 5)}}
        end

      _ ->
        {:error, {:invalid_module, Enum.take(tokens, 5)}}
    end
  end

  defp parse_module_name([{:ident, _, _, name} | rest]) do
    parse_module_name_tail(rest, name)
  end

  defp parse_module_name_tail([{:dot, _, _}, {:ident, _, _, next} | rest], acc) do
    parse_module_name_tail(rest, acc <> "." <> next)
  end

  defp parse_module_name_tail(rest, acc), do: {:ok, acc, rest}

  defp parse_decls([], acc), do: {:ok, Enum.reverse(acc), []}
  defp parse_decls([{:v_right_brace, _, _} | rest], acc), do: {:ok, Enum.reverse(acc), rest}
  defp parse_decls([{:v_semicolon, _, _} | rest], acc), do: parse_decls(rest, acc)

  defp parse_decls(tokens, acc) do
    case parse_decl(tokens) do
      {:ok, decl, rest} -> parse_decls(rest, [decl | acc])
      {:error, _} = err -> err
      _ -> {:ok, Enum.reverse(acc), tokens}
    end
  end

  defp parse_decl([{:data, _, _} | rest]) do
    case rest do
      [{:ident, _, _, name} | rest1] ->
        case parse_type_params(rest1, []) do
          {:ok, params, [{:=, _, _} | rest2]} ->
            case parse_constructors(rest2, []) do
              {:ok, constructors, rest3} ->
                {:ok, %AST.DeclData{name: name, params: params, constructors: constructors},
                 rest3}

              _ ->
                {:error, :invalid_constructors}
            end

          _ ->
            {:error, :invalid_data_params}
        end

      _ ->
        {:error, :invalid_data_decl}
    end
  end

  defp parse_decl([{:ident, _, _, name} | rest]) do
    case parse_binders(rest, []) do
      {:ok, binders, [{:=, _, _} | rest2]} ->
        case parse_expr(rest2) do
          {:ok, expr, rest3} ->
            {:ok, %AST.DeclValue{name: name, binders: binders, expr: expr}, rest3}
        end

      _ ->
        # try as type signature
        case rest do
          [{:colon, _, _} | rest2] ->
            case parse_type(rest2) do
              {:ok, ty, rest3} -> {:ok, %AST.DeclTypeSignature{name: name, type: ty}, rest3}
              _ -> {:error, :invalid_type_sig}
            end

          _ ->
            {:error, :unrecognized_decl}
        end
    end
  end

  defp parse_decl(tokens), do: {:error, :invalid_declaration, Enum.take(tokens, 5)}

  defp parse_type_params([{:ident, _, _, name} | rest], acc),
    do: parse_type_params(rest, [name | acc])

  defp parse_type_params(tokens, acc), do: {:ok, Enum.reverse(acc), tokens}

  defp parse_constructors(tokens, acc) do
    case tokens do
      [{:pipe, _, _} | rest] ->
        parse_constructors(rest, acc)

      _ ->
        case parse_constructor(tokens) do
          {:ok, constr, rest2} -> parse_constructors(rest2, [constr | acc])
          _ -> {:ok, Enum.reverse(acc), tokens}
        end
    end
  end

  defp parse_constructor([{:ident, _, _, name} | rest]) do
    case parse_type_atoms(rest, []) do
      {:ok, args, rest2} -> {:ok, {name, args}, rest2}
      # Constructor with no args
      _ -> {:ok, {name, []}, rest}
    end
  end

  defp parse_constructor(tokens), do: {:error, :no_constructor, Enum.take(tokens, 5)}

  defp parse_type(tokens) do
    case parse_type_atom(tokens) do
      {:ok, t, [{:arrow, _, _} | rest]} ->
        case parse_type(rest) do
          {:ok, t2, rest2} -> {:ok, %AST.Pi{name: "_", domain: t, codomain: t2}, rest2}
          _ -> {:ok, t, rest}
        end

      res ->
        res
    end
  end

  defp parse_type_atom([{:ident, _, _, name} | rest]), do: {:ok, %AST.Var{name: name}, rest}

  defp parse_type_atom([{:left_paren, _, _} | rest]) do
    case parse_type(rest) do
      {:ok, t, [{:right_paren, _, _} | rest2]} -> {:ok, t, rest2}
      err -> err
    end
  end

  defp parse_type_atom(tokens), do: {:error, :no_type_atom, Enum.take(tokens, 5)}

  defp parse_type_atoms(tokens, acc) do
    case parse_type_atom(tokens) do
      {:ok, t, rest} -> parse_type_atoms(rest, [t | acc])
      _ -> {:ok, Enum.reverse(acc), tokens}
    end
  end

  defp parse_binders([{:ident, _, _, name} | rest], acc),
    do: parse_binders(rest, [%AST.Var{name: name} | acc])

  defp parse_binders(tokens, acc), do: {:ok, Enum.reverse(acc), tokens}

  defp parse_expr(tokens) do
    case parse_expr_atom(tokens) do
      {:ok, f, rest} -> parse_expr_app_tail(f, rest)
      err -> err
    end
  end

  defp parse_expr_atom([{:ident, _, _, name} | rest]), do: {:ok, %AST.Var{name: name}, rest}
  defp parse_expr_atom([{:number, _, _, val} | rest]), do: {:ok, %AST.Universe{level: val}, rest}

  defp parse_expr_atom([{:case, _, _} | rest]) do
    case parse_expr(rest) do
      {:ok, e, [{:of, _, _} | rest2]} ->
        case parse_branches(rest2, []) do
          {:ok, branches, rest3} -> {:ok, %AST.Case{expr: e, branches: branches}, rest3}
          err -> err
        end

      _ ->
        {:error, :expected_of}
    end
  end

  defp parse_expr_atom([{:backslash, _, _} | rest]) do
    case parse_binders(rest, []) do
      {:ok, binders, [{:arrow, _, _} | rest2]} ->
        case parse_expr(rest2) do
          {:ok, body, rest3} -> {:ok, %AST.Lambda{binders: binders, body: body}, rest3}
          err -> err
        end

      _ ->
        {:error, :invalid_lambda}
    end
  end

  defp parse_expr_atom([{:left_paren, _, _} | rest]) do
    case parse_expr(rest) do
      {:ok, e, [{:right_paren, _, _} | rest2]} -> {:ok, e, rest2}
      err -> err
    end
  end

  defp parse_expr_atom(tokens), do: {:error, :no_expr_atom, Enum.take(tokens, 5)}

  defp parse_branches([{:v_left_brace, _, _} | rest], acc), do: parse_branches(rest, acc)
  defp parse_branches([{:v_right_brace, _, _} | rest], acc), do: {:ok, Enum.reverse(acc), rest}
  defp parse_branches([{:v_semicolon, _, _} | rest], acc), do: parse_branches(rest, acc)

  defp parse_branches(tokens, acc) do
    case parse_branch(tokens) do
      {:ok, branch, rest} -> parse_branches(rest, [branch | acc])
      _ -> {:ok, Enum.reverse(acc), tokens}
    end
  end

  defp parse_branch(tokens) do
    case parse_pattern(tokens) do
      {:ok, pat, [{:arrow, _, _} | rest]} ->
        case parse_expr(rest) do
          {:ok, body, rest2} -> {:ok, {pat, body}, rest2}
          err -> err
        end

      _ ->
        {:error, :invalid_branch}
    end
  end

  defp parse_pattern([{:ident, _, _, name} | rest]) do
    case parse_patterns_atom(rest, []) do
      {:ok, args, rest2} -> {:ok, %AST.BinderConstructor{name: name, args: args}, rest2}
      _ -> {:ok, %AST.Var{name: name}, rest}
    end
  end

  defp parse_patterns_atom(tokens, acc) do
    case parse_pattern_atom(tokens) do
      {:ok, p, rest} -> parse_patterns_atom(rest, [p | acc])
      _ -> {:ok, Enum.reverse(acc), tokens}
    end
  end

  defp parse_pattern_atom([{:ident, _, _, name} | rest]), do: {:ok, %AST.Var{name: name}, rest}

  defp parse_pattern_atom([{:left_paren, _, _} | rest]) do
    case parse_pattern(rest) do
      {:ok, p, [{:right_paren, _, _} | rest2]} -> {:ok, p, rest2}
      _ -> {:error, :invalid_pattern_paren}
    end
  end

  defp parse_pattern_atom(_), do: {:error, :no_pattern_atom}

  defp parse_expr_app_tail(f, tokens) do
    case parse_expr_atom(tokens) do
      {:ok, arg, rest} -> parse_expr_app_tail(%AST.App{func: f, arg: arg}, rest)
      _ -> {:ok, f, tokens}
    end
  end
end
