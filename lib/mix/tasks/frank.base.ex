defmodule Mix.Tasks.Frank.Base do
  use Mix.Task

  @shortdoc "Compile Frank standard library"
  def run(_) do
    IO.puts("Compiling Frank base library...")

    # Order matters for the base library
    base_files = [
      "priv/frank/Prelude.frank",
      "priv/frank/Data/Unit.frank",
      "priv/frank/Data/Bool.frank",
      "priv/frank/Data/Nat.frank",
      "priv/frank/Data/List.frank",
      "priv/frank/Data/Tree.frank",
      "priv/frank/Data/Fin.frank",
      "priv/frank/Data/Vec.frank",
      "priv/frank/Data/W.frank"
    ]

    out_dir = "ebin"
    File.mkdir_p!(out_dir)

    Enum.each(base_files, fn file ->
      if File.exists?(file) do
        IO.write("  Compiling #{file}... ")
        source = File.read!(file)

        case Frank.Compiler.compile_module(source, source_path: file) do
          {:ok, mod, bin} ->
            beam_path = Path.join(out_dir, "#{mod}.beam")
            File.write!(beam_path, bin)
            IO.puts("OK")

          {:error, _reason} ->
            IO.puts("FAILED")
        end
      end
    end)

    IO.puts("\nFrank base library compilation finished.")
  end
end
