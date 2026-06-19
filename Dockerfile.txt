FROM python:3.11-slim

WORKDIR /app

# Copy requirements first for better caching
COPY requirements.txt .

# Force reinstall packages with no cache
RUN pip install --no-cache-dir --upgrade pip
RUN pip install --no-cache-dir -r requirements.txt --force-reinstall

# Copy all application files
COPY earnplusd.py .
COPY *.py .

# Run the bot
CMD ["python", "earnplusd.py"]
