import os
import sys
import bitcoinrpc
from bitcoinrpc.authproxy import AuthServiceProxy
def get_rpc_connection():
    rpc_user = "rpcuser"
    rpc_password = "rpcpassword"
    rpc_host = os.environ.get("BITCOIN_RPC_HOST", "127.0.0.1")
    rpc_port = os.environ.get("BITCOIN_RPC_PORT", "8332")
    connection_url = f"http://{rpc_user}:{rpc_password}@{rpc_host}:{rpc_port}"
    return AuthServiceProxy(connection_url)
def extract_data(rpc_connection, start_block=0):
    block_count = rpc_connection.getblockcount()
    print(f"Block count: {block_count}")
    block_hashes = []
    merkle_roots = []
    tx_hashes = []
    chainwork_values = []
    for i in range(start_block, block_count + 1):
        try:
            block_hash = rpc_connection.getblockhash(i)
            block = rpc_connection.getblock(block_hash)
            block_hashes.append(block_hash)
            merkle_roots.append(block["merkleroot"])
            chainwork_values.append(block["chainwork"])
            for tx in block["tx"]:
                tx_hashes.append(tx)
            # Save data for every block
            write_to_files(block_hashes, merkle_roots, tx_hashes, chainwork_values, start_block=i)
            block_hashes.clear()
            merkle_roots.clear()
            tx_hashes.clear()
            chainwork_values.clear()
            sys.stdout.write(f"\rProcessed block: {i}")
            sys.stdout.flush()
        except Exception as e:
            print(f"\nError at block {i}: {e}")
            break
    return block_hashes, merkle_roots, tx_hashes, chainwork_values
def write_to_files(block_hashes, merkle_roots, tx_hashes, chainwork_values, start_block=0):
    with open("block_hashes.txt", "a") as hash_file, open("merkle_roots.txt", "a") as merkle_file, open("transaction_hashes.txt", "a") as tx_file, open("chainwork_values.txt", "a") as chainwork_file:
        for block_hash in block_hashes:
            hash_file.write(f"{block_hash}\n")
        
        for merkle_root in merkle_roots:
            merkle_file.write(f"{merkle_root}\n")
        
        for tx_hash in tx_hashes:
            tx_file.write(f"{tx_hash}\n")
        
        for chainwork_value in chainwork_values:
            chainwork_file.write(f"{chainwork_value}\n")
if __name__ == "__main__":
    rpc_connection = get_rpc_connection()
    block_hashes, merkle_roots, tx_hashes, chainwork_values = extract_data(rpc_connection)
