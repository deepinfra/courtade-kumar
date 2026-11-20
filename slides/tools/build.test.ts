import { beforeAll, expect, test } from "bun:test";
import { file, spawn } from "bun";
import { readdir } from "node:fs/promises";
import { tmpdir } from "node:os";
import { resolve } from "node:path";
import { brotliDecompressSync, gunzipSync } from "node:zlib";
import { buildSlides } from "./build";
import { contentHash } from "./hash";
import { BundleRoot, SlidesRoot } from "./paths";
import { serveBundle } from "./server";

let html: string;
let names: string[];

beforeAll(async () => {
  await buildSlides();
  html = await file(`${BundleRoot}/index.html`).text();
  names = (await readdir(BundleRoot)).sort();
});

test("ships both slides with no browser math renderer", async () => {
  expect(html.match(/<section\b/g)).toHaveLength(2);
  expect(html).toContain("Dimiter Kramer");
  expect(html).toContain("Mert Saglam");
  expect(html).not.toContain("$");
  expect(html).not.toContain("build:");
  expect(html).toMatch(/<script[^>]+type=module/);
  for (const name of names.filter((name) => name.endsWith(".js"))) {
    const script = await file(`${BundleRoot}/${name}`).text();
    expect(script).not.toContain("lacolon");
    expect(script).not.toContain("renderParagraph");
  }
});

test("all referenced assets are flat, root-relative, and hashed from emitted bytes", async () => {
  for (const name of names.filter((name) => /\.(js|css|woff2?)$/.test(name))) {
    const bytes = await file(`${BundleRoot}/${name}`).bytes();
    expect(name.split(".")[0]).toBe(contentHash(bytes));
  }
  const references = [...html.matchAll(/(?:src|href)=([^\s>]+)/g)]
    .map((match) => match[1].replaceAll('"', ""))
    .filter((url) => !url.startsWith("https:") && !url.startsWith("data:"));
  for (const name of names.filter((name) => name.endsWith(".css"))) {
    const css = await file(`${BundleRoot}/${name}`).text();
    references.push(...[...css.matchAll(/url\(([^)]+)\)/g)]
      .map((match) => match[1].replaceAll('"', ""))
      .filter((url) => !url.startsWith("data:") && !url.startsWith("#")));
  }
  expect(references.length).toBeGreaterThanOrEqual(5);
  for (const url of references) {
    expect(url).toMatch(/^\/[A-Za-z0-9_-]{8}\.(js|css|woff2?)$/);
    expect(names).toContain(url.slice(1));
    expect(new URL(url, "https://example.test/talks/courtade-kumar").pathname).toBe(url);
  }
});

test("gzip and Brotli variants decode to exactly the emitted assets", async () => {
  for (const name of names.filter((name) => /\.(html|js|css)$/.test(name))) {
    const bytes = Buffer.from(await file(`${BundleRoot}/${name}`).bytes());
    expect(gunzipSync(await file(`${BundleRoot}/${name}.gz`).bytes())).toEqual(bytes);
    expect(brotliDecompressSync(await file(`${BundleRoot}/${name}.br`).bytes())).toEqual(bytes);
  }
});

test("serves the entry, root assets, HEAD requests, and genuine missing-file responses", async () => {
  const request = (path: string, method = "GET") =>
    serveBundle(new Request(`http://localhost${path}`, { method }));
  const page = await request("/");
  expect(page.status).toBe(200);
  expect(page.headers.get("Content-Type")).toContain("text/html");
  expect(await page.text()).toBe(html);
  for (const name of names.filter((name) => /\.(js|css|woff2?)$/.test(name))) {
    const response = await request(`/${name}`);
    expect(response.status).toBe(200);
    expect(response.headers.get("Content-Type")).not.toContain("text/html");
    expect(await response.arrayBuffer()).toEqual(await file(`${BundleRoot}/${name}`).arrayBuffer());
  }
  expect(await (await request("/index.html", "HEAD")).text()).toBe("");
  expect((await request("/missing.js")).status).toBe(404);
  expect((await request("/entry/entry.ts")).status).toBe(404);
  expect((await request("/%zz")).status).toBe(400);
  expect((await request("/", "POST")).status).toBe(405);
});

test("building from outside the package produces the same bundle", async () => {
  const before = await Promise.all(names.map(async (name) =>
    [name, contentHash(await file(`${BundleRoot}/${name}`).bytes())]));
  const buildProcess = spawn([process.execPath, resolve(SlidesRoot, "tools/build.ts")], {
    cwd: tmpdir(),
    stdout: "pipe",
    stderr: "pipe",
  });
  const error = await new Response(buildProcess.stderr).text();
  expect(await buildProcess.exited, error).toBe(0);
  expect((await readdir(BundleRoot)).sort()).toEqual(names);
  const after = await Promise.all(names.map(async (name) =>
    [name, contentHash(await file(`${BundleRoot}/${name}`).bytes())]));
  expect(after).toEqual(before);
});
