defmodule Frank.Type do
  @moduledoc """
  Helper functions for Frank types.
  In Frank (CIC), everything is a term, so these are utilities for AST terms.
  """
  alias Frank.AST

  def pi(name, domain, codomain) do
    %AST.Pi{name: name, domain: domain, codomain: codomain}
  end

  def arrow(a, b) do
    %AST.Pi{name: "_", domain: a, codomain: b}
  end

  def universe(i), do: %AST.Universe{level: i}

  # Common types
  def nat(), do: %AST.Var{name: "Nat"}
  def bool(), do: %AST.Var{name: "Bool"}
  def unit(), do: %AST.Var{name: "Unit"}
end
