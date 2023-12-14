## Movement Subnet
Currently deployed on the Avalanche Fuji network, you can access it through the following script

### Subnet and Move EVM Explorer

```bash
https://explorer.devnet.m1.movementlabs.xyz
```

### Subnet Native Token Faucet and Birdge

```bash
https://faucet.devnet.m1.movementlabs.xyz
```

### Subnet Chain ID
```
2vUTKYZBbLtXnfCL2RF5XEChZf1wxVYQqxZQQCShMmseSKSiee
```
### Subnet JSON-RPC Endpoint
```
https://subnet.devnet.m1.movementlabs.xyz/v1
```

```bash
curl -X POST --data '{
  "jsonrpc": "2.0",
  "id"     : 1,
  "method" : "getTransactionByHash",
  "params" : [{"data":"1f073fce3c2390d68a95289dc81df9dad1d0fa07541da5da4e1b46241f4bd24e"}]
}' -H 'content-type:application/json;'  https://subnet.devnet.m1.movementlabs.xyz/v1/ext/bc/2vUTKYZBbLtXnfCL2RF5XEChZf1wxVYQqxZQQCShMmseSKSiee/rpc

```

### Subnet Restful Endpoint

```
https://devnet.m1.movementlabs.xyz/v1
```

```javascript
const { AptosClient } = require("aptos");
const NODE_URL = "https://devnet.m1.movementlabs.xyz/v1";
const client = new AptosClient(NODE_URL);

getLedgerInfo();

async function getLedgerInfo() {
    let info = await client.getLedgerInfo();
    console.log(info);
}

```
```
{
  chain_id: 4,
  epoch: '35',
  ledger_version: '1375',
  oldest_ledger_version: '0',
  ledger_timestamp: '1702359642904612',
  node_role: 'validator',
  oldest_block_height: '0',
  block_height: '481',
  git_hash: '656c604422eb6d3ef21831adc0c18bf77ddf8767'
}
```

### Move Evm JSON-RPC Endpoint
> chainId 336 (0x150)

```bash
https://mevm.devnet.m1.movementlabs.xyz/v1
```

```javascript
const { Web3 } = require("web3");

getTransactionReceipt();

async function getTransactionReceipt() {
    const web3 = new Web3(new Web3.providers.HttpProvider("https://mevm.devnet.m1.movementlabs.xyz/v1"));
    const res = await web3.eth.getTransactionReceipt(
        "0x43465b887a3f4655f80b1b241ce08164f77a29ea704b6bcfd5004031c1982ff9"
    );
    console.log(res);
}
```

```
{
  blockHash: '0xc10eda86c48a12b2c8dcbe61c786409a3b1602df03458167a531a59f580cb0bc',
  blockNumber: 458n,
  cumulativeGasUsed: 0n,
  effectiveGasPrice: 0n,
  from: '0xedd3bce148f5acffd4ae7589d12cf51f7e4788c6',
  gasUsed: 919n,
  logs: [],
  to: '0x3dc950aceda4cafb74d38530e839cca58dda527d',
  logsBloom: '0x00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000',
  status: 1n,
  transactionHash: '0x43465b887a3f4655f80b1b241ce08164f77a29ea704b6bcfd5004031c1982ff9',
  transactionIndex: 0n,
  type: 0n
}
```
