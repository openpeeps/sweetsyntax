export function parseScript(code: string, ext: string): any;
export function parseFileScript(path: string): any;
export function highlightScript(code: string, ext: string, format: string): string;
export function highlightFileScript(path: string, format: string): string;

export const binaryPath: string;
export const nativePair: string;
