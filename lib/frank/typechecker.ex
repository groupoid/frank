defmodule Frank.Typechecker do
  alias Frank.AST

  @doc """
  Typing environment contains:
  - env: map of (name -> inductive)
  - ctx: list of (name, type)
  """
  defmodule Env do
    defstruct env: %{}, ctx: [], defs: %{}
  end

  def infer(%Env{} = e, %AST.Var{name: name}) do
    case List.keyfind(e.ctx, name, 0) do
      {^name, ty} -> ty
      nil -> {:error, {:unbound_variable, name}}
    end
  end

  def infer(%Env{}, %AST.Universe{level: i}) do
    %AST.Universe{level: i + 1}
  end

  def infer(%Env{} = _e, %AST.Inductive{level: level}) do
    %AST.Universe{level: level + 1}
  end

  def infer(%Env{} = e, %AST.Constr{index: j, inductive: d, args: args}) do
    {^j, ty} = List.keyfind(d.constrs, j, 0)
    ty_subst = subst_many(d.params, ty)
    infer_ctor(e, ty_subst, args)
  end

  def infer(%Env{} = e, %AST.Ind{inductive: _d, motive: p, cases: _cases, term: t}) do
    _t_ty = infer(e, t)
    # Check if t_ty is the inductive type d applied to its params
    # This is a simplified check for now
    %AST.Pi{name: x, domain: _a, codomain: b} = p
    # result type is motive applied to t
    subst(x, t, b)
  end

  def infer(%Env{} = e, %AST.Pi{name: x, domain: a, codomain: b}) do
    u_a = universe_level(e, a)
    u_b = universe_level(%{e | ctx: [{x, a} | e.ctx]}, b)
    %AST.Universe{level: max(u_a, u_b)}
  end

  def infer(%Env{} = e, %AST.Lam{name: x, domain: domain, body: body}) do
    # check(e, domain, ...)
    %AST.Pi{name: x, domain: domain, codomain: infer(%{e | ctx: [{x, domain} | e.ctx]}, body)}
  end

  def infer(%Env{} = e, %AST.App{func: f, arg: arg}) do
    case infer(e, f) do
      %AST.Pi{name: x, domain: a, codomain: b} ->
        check(e, arg, a)
        subst(x, arg, b)

      _ ->
        {:error, :application_requires_pi}
    end
  end

  def check(%Env{} = e, t, ty) do
    inferred = infer(e, t)

    if equal?(e, inferred, ty) do
      :ok
    else
      {:error, {:type_mismatch, inferred, ty}}
    end
  end

  def universe_level(e, t) do
    case normalize(e, t) do
      %AST.Universe{level: i} -> i
      _ -> raise "Expected universe, got #{inspect(t)}"
    end
  end

  def equal?(e, t1, t2) do
    normalize(e, t1) == normalize(e, t2)
  end

  def normalize(e, t) do
    t_red = reduce(e, t)

    case t_red do
      %AST.App{func: f, arg: arg} ->
        # After reducing the application as much as possible,
        # we recursively normalize the parts.
        %AST.App{func: normalize(e, f), arg: normalize(e, arg)}

      %AST.Lam{name: x, domain: a, body: b} ->
        %AST.Lam{name: x, domain: normalize(e, a), body: normalize(e, b)}

      %AST.Pi{name: x, domain: a, codomain: b} ->
        %AST.Pi{name: x, domain: normalize(e, a), codomain: normalize(e, b)}

      %AST.Ind{inductive: d, motive: p, cases: cases, term: t_val} ->
        %AST.Ind{
          inductive: d,
          motive: normalize(e, p),
          cases: Enum.map(cases, &normalize(e, &1)),
          term: normalize(e, t_val)
        }

      %AST.Constr{index: i, inductive: d, args: args} ->
        %AST.Constr{index: i, inductive: d, args: Enum.map(args, &normalize(e, &1))}

      _ ->
        t_red
    end
  end

  def reduce(e, %AST.App{func: f, arg: arg}) do
    f_red = reduce(e, f)

    case f_red do
      %AST.Lam{name: x, body: body} ->
        # Beta reduction: (\x -> body) arg => reduce(body[x := arg])
        reduce(e, subst(x, arg, body))

      _ ->
        %AST.App{func: f_red, arg: arg}
    end
  end

  def reduce(e, %AST.Ind{inductive: _d, motive: _p, cases: cases, term: t} = ind) do
    case reduce(e, t) do
      %AST.Constr{index: j, args: args} ->
        case_val = Enum.at(cases, j - 1)
        res = apply_args(e, case_val, args, ind)
        # Result of Ind could be another reducible term
        reduce(e, res)

      _ ->
        ind
    end
  end

  def reduce(e, %AST.Let{decls: decls, body: body}) do
    new_defs =
      Enum.reduce(decls, e.defs, fn {n, expr}, acc ->
        Map.put(acc, n, expr)
      end)

    reduce(%{e | defs: new_defs}, body)
  end

  def reduce(e, %AST.Var{name: name}) do
    # IO.puts("Looking up: #{name}")
    case Map.get(e.defs, name) do
      nil ->
        %AST.Var{name: name}

      term ->
        reduce(e, term)
    end
  end

  def reduce(_e, t), do: t

  defp apply_args(_e, f, [], _ind), do: f

  defp apply_args(e, f, [arg | rest], %AST.Ind{} = ind) do
    # For each arg, if it's of the inductive type, the case expects (arg, ih)
    f_next = %AST.App{func: f, arg: arg}

    # Desugarer: \k -> \ih -> ...
    ih = %AST.Ind{ind | term: arg}
    f_with_ih = %AST.App{func: f_next, arg: ih}
    apply_args(e, f_with_ih, rest, ind)
  end

  def subst_many(params, ty) do
    Enum.reduce(params, ty, fn {name, val}, acc -> subst(name, val, acc) end)
  end

  defp infer_ctor(e, ty, args) do
    Enum.reduce(args, ty, fn arg, acc ->
      case acc do
        %AST.Pi{name: x, domain: a, codomain: b} ->
          check(e, arg, a)
          subst(x, arg, b)

        _ ->
          raise "Too many arguments to constructor"
      end
    end)
  end

  def subst(x, s, %AST.Var{name: name}) do
    if name == x, do: s, else: %AST.Var{name: name}
  end

  def subst(x, s, %AST.Pi{name: n, domain: a, codomain: b}) do
    if n == x do
      %AST.Pi{name: n, domain: subst(x, s, a), codomain: b}
    else
      %AST.Pi{name: n, domain: subst(x, s, a), codomain: subst(x, s, b)}
    end
  end

  def subst(x, s, %AST.Lam{name: n, domain: a, body: b}) do
    if n == x do
      %AST.Lam{name: n, domain: subst(x, s, a), body: b}
    else
      %AST.Lam{name: n, domain: subst(x, s, a), body: subst(x, s, b)}
    end
  end

  def subst(x, s, %AST.App{func: f, arg: arg}) do
    %AST.App{func: subst(x, s, f), arg: subst(x, s, arg)}
  end

  def subst(x, s, %AST.Let{decls: decls, body: body}) do
    new_decls = Enum.map(decls, fn {name, expr} -> {name, subst(x, s, expr)} end)
    %AST.Let{decls: new_decls, body: subst(x, s, body)}
  end

  def subst(x, s, %AST.Ind{inductive: d, motive: p, cases: cases, term: t}) do
    # Also subst in inductive params if needed
    %AST.Ind{
      inductive: d,
      motive: subst(x, s, p),
      cases: Enum.map(cases, &subst(x, s, &1)),
      term: subst(x, s, t)
    }
  end

  def subst(x, s, %AST.Constr{index: i, inductive: d, args: args}) do
    %AST.Constr{index: i, inductive: d, args: Enum.map(args, &subst(x, s, &1))}
  end

  def subst(_, _, t), do: t
end
