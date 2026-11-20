import { build, file, spawn, write } from "bun";
import { mkdir, rm } from "node:fs/promises";
import { resolve } from "node:path";
import { fileURLToPath } from "node:url";
import { minify } from "html-minifier-terser";
import { renderParagraph } from "../latex/latex";
import { Fonts } from "../gito/gito";
import { contentHash } from "./hash";
import { brotli, gzip } from "./compress";
import htmlMinifierOptions from "./htmlminifier";
import { BundleRoot, SlidesRoot } from "./paths";

// Explicit cascade order until components declare their styles through TSX imports.
const Stylesheets = [
  "gito/gito.css",
  "reveal/reveal.css",
  "latex/latex.css",
  "title/title.css",
  "entry/entry.css",
];

/** One HTML entry and flat assets, independent of the caller's working directory. */
export const buildSlides = async (): Promise<void> => {
  const script = resolve(SlidesRoot, "build/js/entry.js");
  await mkdir(resolve(SlidesRoot, "build/js"), { recursive: true });
  const compiler = spawn([
    process.execPath,
    fileURLToPath(import.meta.resolve("@kimlikdao/kdts/kdts.js")),
    "entry/entry.ts", "--fast", "--packages", "external", "--output", script,
  ], {
    cwd: SlidesRoot,
    stdout: "pipe",
    stderr: "pipe",
  });
  const [status, stdout, stderr] = await Promise.all([
    compiler.exited,
    new Response(compiler.stdout).text(),
    new Response(compiler.stderr).text(),
  ]);
  if (status !== 0)
    throw new Error(`kdts --fast failed (${status})\n${stdout}${stderr}`);

  const stylesheet = resolve(SlidesRoot, "build/css/entry.css");
  await mkdir(resolve(SlidesRoot, "build/css"), { recursive: true });
  await write(stylesheet, (await Promise.all(Stylesheets.map((path) =>
    file(resolve(SlidesRoot, path)).text()))).join("\n"));

  // Keep npm dependencies outside kdts's optimizations, then bundle them here.
  const result = await build({
    entrypoints: [script, stylesheet],
    target: "browser",
    format: "esm",
    minify: true,
    publicPath: "/",
    external: ["*.woff", "*.woff2"],
  });
  if (!result.success)
    throw new AggregateError(result.logs, "Slides build failed");

  const assets = new Map<string, Uint8Array>();
  const addAsset = (bytes: Uint8Array, extension: string): string => {
    const name = `${contentHash(bytes)}.${extension}`;
    assets.set(name, bytes);
    return `/${name}`;
  };
  const fonts = new Map<string, string>();
  for (const filename of Fonts) {
    const path = resolve(SlidesRoot, "gito", filename);
    const extension = filename.slice(filename.lastIndexOf(".") + 1);
    fonts.set(filename, addAsset(await file(path).bytes(), extension));
  }

  let html = renderParagraph(await file(resolve(SlidesRoot, "entry/entry.html")).text());
  if (html.includes("$"))
    throw new Error("Unmatched math delimiters in entry/entry.html");

  for (const extension of ["css", "js"]) {
    const output = result.outputs.find((asset) =>
      asset.path.endsWith(`.${extension}`));
    if (!output)
      throw new Error(`Missing ${extension} entry bundle`);
    let content = await output.text();
    if (extension === "css") {
      for (const [alias, url] of fonts)
        content = content.replaceAll(alias, url);
    }
    const url = addAsset(new TextEncoder().encode(content), extension);
    const element = extension === "css"
      ? `<link rel="stylesheet" href="${url}">`
      : `<script type="module" src="${url}"></script>`;
    const marker = new RegExp(`<!-- build:${extension} -->[\\s\\S]*?<!-- endbuild -->`);
    if (!marker.test(html))
      throw new Error(`Missing build:${extension} marker in entry/entry.html`);
    html = html.replace(marker, element);
  }

  html = await minify(html, htmlMinifierOptions);

  await rm(BundleRoot, { recursive: true, force: true });
  await mkdir(BundleRoot, { recursive: true });

  const emit = async (name: string, bytes: Uint8Array): Promise<void> => {
    const destination = resolve(BundleRoot, name);
    await write(destination, bytes);
    if (/\.(html|js|css|svg|woff|ttf)$/.test(name)) {
      await Promise.all([
        gzip(destination, destination),
        brotli(destination, destination),
      ]);
    }
  };
  await Promise.all([...assets].map(([name, bytes]) => emit(name, bytes)));
  await emit("index.html", new TextEncoder().encode(html));
  console.log(`Built ${BundleRoot}/index.html (${assets.size} hashed assets)`);
};

if (import.meta.main)
  await buildSlides();
