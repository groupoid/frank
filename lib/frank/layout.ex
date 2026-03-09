defmodule Frank.Layout do
  def resolve(tokens) do
    # For now, just return tokens as is, plus a virtual layer
    # if we want to support significant whitespace.
    # To stabilize tests, let's implement a MINIMAL version
    # that only inserts virtual braces for the module if they aren't there.
    case tokens do
      [{:module, _, _} | _] ->
        [{:v_left_brace, 1, 1} | tokens] ++ [{:v_right_brace, 999, 1}]

      _ ->
        tokens
    end
  end
end
