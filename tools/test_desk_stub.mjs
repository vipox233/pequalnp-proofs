// A stub of the desk for tools/test_pnp_cause.sh: node tools/test_desk_stub.mjs <dir>
// Listens on 127.0.0.1 on a free port, writes its pid to <dir>/pid and the port to <dir>/port, and answers each request from <dir>/routes.json,
// {"<METHOD> <path>": {"status": <n>, "body": <json>}}, read again on every request so a test can change it between calls.
// Every request is logged to <dir>/log as "<METHOD> <path>?<query>", and a request body is kept as <dir>/body.<n>.
// An unknown route answers 404. Nothing here reaches any other host.
import fs from 'node:fs';
import http from 'node:http';
import path from 'node:path';

const dir = process.argv[2];
let n = 0;
const server = http.createServer((req, res) => {
  const chunks = [];
  req.on('data', (c) => chunks.push(c));
  req.on('end', () => {
    const url = new URL(req.url, 'http://127.0.0.1');
    fs.appendFileSync(path.join(dir, 'log'), `${req.method} ${url.pathname}${url.search}\n`);
    if (chunks.length) fs.writeFileSync(path.join(dir, `body.${++n}`), Buffer.concat(chunks));
    let routes = {};
    try { routes = JSON.parse(fs.readFileSync(path.join(dir, 'routes.json'), 'utf8')); } catch { /* no routes yet */ }
    const r = routes[`${req.method} ${url.pathname}`] ?? { status: 404, body: { error: 'unknown' } };
    res.writeHead(r.status, { 'content-type': 'application/json' });
    res.end(typeof r.body === 'string' ? r.body : JSON.stringify(r.body));
  });
});
server.listen(0, '127.0.0.1', () => { fs.writeFileSync(path.join(dir, 'pid'), String(process.pid)); fs.writeFileSync(path.join(dir, 'port'), String(server.address().port)); });
// A plain exit on SIGTERM: a launcher shim that re-raises a child's signal death would take the test's shell with it.
process.on('SIGTERM', () => process.exit(0));
