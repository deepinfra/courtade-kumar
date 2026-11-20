import { argv, file, spawn, write } from "bun";
import { rename, rm, utimes } from "node:fs/promises";

const ConstantTime = new Date("2026-01-01T00:00:00");

const run = async (cmd: string[]): Promise<void> => {
  const process = spawn({ cmd, stdout: "pipe", stderr: "pipe" });
  if (await process.exited != 0)
    throw new Error(`${cmd[0]} failed: ${await new Response(process.stderr).text()}`);
};

const gzip = async (inputName: string, outputName: string): Promise<string> => {
  const outputNameExt = outputName + ".gz";
  const temporary = outputNameExt + ".tmp";
  await write(temporary, file(inputName));
  await utimes(temporary, ConstantTime, ConstantTime);
  try {
    await run([
      "zopfli",
      "--force",
      "--best",
      "--i20",
      temporary,
    ]);
    await rename(temporary + ".gz", outputNameExt);
  } finally {
    await rm(temporary, { force: true });
    await rm(temporary + ".gz", { force: true });
  }
  return outputNameExt;
};

const brotli = async (inputName: string, outputName: string): Promise<string> => {
  const outputNameExt = outputName + ".br";
  console.info(`brotli: ${outputName}.br <- ${inputName}`);
  await run([
    "brotli",
    "--force",
    "-w", "24",
    "--quality=11",
    "--no-copy-stat",
    `--output=${outputNameExt}`,
    inputName,
  ]);
  return outputNameExt;
};

if (import.meta.main) {
  const method = argv[2];
  const inputName = argv[3];
  const outputName = argv[4];
  if (!inputName || !outputName)
    throw new Error("Usage: bun tools/compress.ts <gzip|brotli> <input> <output>");
  if (method == "gzip")
    await gzip(inputName, outputName);
  else if (method == "brotli")
    await brotli(inputName, outputName);
  else
    throw new Error(`Unknown compression method: ${method}`);
}

export { brotli, gzip };
