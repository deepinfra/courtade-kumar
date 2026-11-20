import { hash } from "bun";

/** Same 48-bit, eight-character base64url content hash as the homepage. */
export const contentHash = (bytes: Uint8Array): string => {
  const buffer = new ArrayBuffer(8);
  new DataView(buffer).setBigUint64(0, hash(bytes));
  return Buffer.from(buffer, 2).toString("base64url");
};
