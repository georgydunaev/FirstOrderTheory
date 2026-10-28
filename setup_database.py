import sqlite3

# Connect to the database
conn = sqlite3.connect('search_database.db')
cursor = conn.cursor()

# Create the terms table
cursor.execute('''CREATE TABLE IF NOT EXISTS terms (id INTEGER PRIMARY KEY, term TEXT)''')

# Insert some sample data
cursor.execute("INSERT INTO terms (term) VALUES ('sample query')")

# Commit changes and close the connection
conn.commit()
conn.close()
