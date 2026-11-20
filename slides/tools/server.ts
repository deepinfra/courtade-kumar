import { env, file, serve } from "bun";
import { buildSlides } from "./build";
import { BundleRoot } from "./paths";

/** Serve only the built entry and its flat public assets. */
export const serveBundle = async (request: Request): Promise<Response> => {
  if (request.method !== "GET" && request.method !== "HEAD")
    return new Response("Method not allowed", { status: 405, headers: { Allow: "GET, HEAD" } });

  let pathname: string;
  try {
    pathname = decodeURIComponent(new URL(request.url).pathname);
  } catch {
    return new Response("Bad request", { status: 400 });
  }
  const name = pathname === "/" ? "index.html" : pathname.slice(1);
  if (!/^[A-Za-z0-9_-]+\.(html|js|css|svg|woff2?|ttf|png|webp|jpg|jpeg)$/.test(name))
    return new Response("Not found", { status: 404 });

  const asset = file(`${BundleRoot}/${name}`);
  if (!(await asset.exists()))
    return new Response("Not found", { status: 404 });
  return new Response(request.method === "HEAD" ? null : asset, {
    headers: {
      "Content-Type": asset.type,
      "Cache-Control": "no-store",
    },
  });
};

if (import.meta.main) {
  if (process.argv.includes("--build"))
    await buildSlides();
  if (!(await file(`${BundleRoot}/index.html`).exists()))
    throw new Error("Build the slides first: bun run build");
  const server = serve({
    hostname: "127.0.0.1",
    port: Number(env["SLIDES_PORT"] || 8001),
    fetch: serveBundle,
  });
  console.log(`Serving CK slides at ${server.url}`);
}
