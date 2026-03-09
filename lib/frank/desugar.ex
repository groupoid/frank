defmodule Frank.Desugar do
  alias Frank.AST

  def desugar(%AST.Module{declarations: decls} = m, env \\ %Frank.Typechecker.Env{}) do
    # Pass env to desugar_decl if needed, though for now only REPL uses it
    %AST.Module{m | declarations: Enum.map(decls, &desugar_decl(&1, env))}
  end

  def desugar_decl(decl, env \\ %Frank.Typechecker.Env{})

  def desugar_decl(
        %AST.DeclValue{name: name, binders: binders, expr: expr, where_decls: where_decls},
        env
      ) do
    # Desugar local where_decls first
    desugared_where = Enum.map(where_decls || [], &desugar_decl(&1, env))

    # Convert to Let if there are any where_decls
    expr_with_where =
      if desugared_where == [] do
        expr
      else
        decls_list = Enum.map(desugared_where, fn d -> {d.name, d.expr} end)
        %AST.Let{decls: decls_list, body: expr}
      end

    # Transform f x y = e into f = \x -> \y -> e
    body =
      Enum.reduce(Enum.reverse(binders), desugar_expression(expr_with_where, env, name), fn
        %AST.Var{name: vn}, acc ->
          %AST.Lam{name: vn, domain: %AST.Universe{level: 0}, body: acc}
      end)

    %AST.DeclValue{name: name, binders: [], expr: body}
  end

  def desugar_decl(%AST.DeclData{name: name, params: params, constructors: constructors}, _env) do
    # ... (remains same logic but needs to be grouped)
    ind_params = Enum.map(params, fn p -> {p, %AST.Universe{level: 0}} end)

    constrs =
      Enum.with_index(constructors, 1)
      |> Enum.map(fn {{cname, args}, idx} ->
        ty =
          Enum.reduce(Enum.reverse(args), %AST.Var{name: name}, fn arg, acc ->
            %AST.Pi{name: "_", domain: arg, codomain: acc}
          end)

        {idx, cname, ty}
      end)

    %AST.Inductive{name: name, params: ind_params, level: 0, constrs: constrs}
  end

  def desugar_decl(decl, _env), do: decl

  def desugar_expression(expr, env \\ %{}, func_name \\ nil) do
    case expr do
      %AST.Lambda{binders: binders, body: body} ->
        Enum.reduce(Enum.reverse(binders), desugar_expression(body, env, func_name), fn
          %AST.Var{name: vn}, acc ->
            %AST.Lam{name: vn, domain: %AST.Universe{level: 0}, body: acc}
        end)

      %AST.Case{expr: e, branches: branches} ->
        # Find inductive type from the first branch
        ind =
          if branches == [] do
            %AST.Inductive{name: "Empty", params: [], level: 0, constrs: []}
          else
            {first_pat, _} = hd(branches)

            case first_pat do
              %AST.BinderConstructor{name: cname} ->
                # Search in env.env for an inductive that has this constructor
                Enum.find_value(Map.values(env.env), fn ind ->
                  if Enum.any?(ind.constrs, fn {_, name, _} -> name == cname end), do: ind
                end)

              _ ->
                nil
            end
          end

        # Fallback to Nat if not found (for the demo)
        ind =
          ind ||
            %AST.Inductive{
              name: "Nat",
              params: [],
              level: 0,
              constrs: [
                {1, "Zero", %AST.Var{name: "Nat"}},
                {2, "Succ",
                 %AST.Pi{
                   name: "_",
                   domain: %AST.Var{name: "Nat"},
                   codomain: %AST.Var{name: "Nat"}
                 }}
              ]
            }

        desugared_target = desugar_expression(e, env, func_name)

        # Map branches to Ind cases
        # Ind cases MUST be in the same order as in ind.constrs
        cases =
          Enum.map(ind.constrs, fn {_idx, cname, _cty} ->
            # Find a branch for this constructor
            branch =
              Enum.find(branches, fn {pat, _} ->
                case pat do
                  %AST.BinderConstructor{name: ^cname} -> true
                  _ -> false
                end
              end)

            case branch do
              {pat, body} ->
                # If constructor has args, wrap in lambdas
                case pat do
                  %AST.BinderConstructor{args: args} when args != [] ->
                    Enum.reduce(Enum.reverse(args), desugar_expression(body, env, func_name), fn
                      %AST.Var{name: k}, acc ->
                        ih_name = "ih_#{k}"
                        # Recursive call replacement
                        acc_with_ih = replace_recursion(acc, func_name, k, ih_name)

                        %AST.Lam{
                          name: k,
                          domain: %AST.Universe{level: 0},
                          body: %AST.Lam{
                            name: ih_name,
                            domain: %AST.Universe{level: 0},
                            body: acc_with_ih
                          }
                        }
                    end)

                  _ ->
                    desugar_expression(body, env, func_name)
                end

              _ ->
                # Missing branch?
                %AST.Var{name: "missing_branch_#{cname}"}
            end
          end)

        %AST.Ind{
          inductive: ind,
          motive: %AST.Lam{name: "_", domain: ind, body: %AST.Universe{level: 0}},
          cases: cases,
          term: desugared_target
        }

      %AST.App{func: f, arg: arg} ->
        %AST.App{
          func: desugar_expression(f, env, func_name),
          arg: desugar_expression(arg, env, func_name)
        }

      %AST.Let{decls: decls, body: let_body} ->
        decls_desugared =
          Enum.map(decls, fn {n, e} ->
            {n, desugar_expression(e, env, n)}
          end)

        %AST.Let{
          decls: decls_desugared,
          body: desugar_expression(let_body, env, func_name)
        }

      _ ->
        expr
    end
  end

  defp replace_recursion(expr, func_name, k, ih_name) do
    # Try to match (func_name ... k ...)
    case expr do
      # Match f k
      %AST.App{func: %AST.Var{name: ^func_name}, arg: %AST.Var{name: ^k}} ->
        %AST.Var{name: ih_name}

      # Match (f (g x)) y -> (ih x)
      %AST.App{
        func: %AST.App{
          func: %AST.Var{name: ^func_name},
          arg: %AST.App{func: %AST.Var{name: ^k}, arg: arg}
        },
        arg: _
      } ->
        %AST.App{func: %AST.Var{name: ih_name}, arg: arg}

      # Match (f x) k
      %AST.App{func: %AST.App{func: %AST.Var{name: ^func_name}, arg: _x}, arg: %AST.Var{name: ^k}} ->
        %AST.Var{name: ih_name}

      # Match (f k) y
      %AST.App{func: %AST.App{func: %AST.Var{name: ^func_name}, arg: %AST.Var{name: ^k}}, arg: _y} ->
        %AST.Var{name: ih_name}

      %AST.App{func: f, arg: arg} ->
        %AST.App{
          func: replace_recursion(f, func_name, k, ih_name),
          arg: replace_recursion(arg, func_name, k, ih_name)
        }

      _ ->
        expr
    end
  end
end
