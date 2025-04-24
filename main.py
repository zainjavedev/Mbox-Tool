import sys
import os
import re
import mailbox
import email
import email.header
import tkinter as tk
from tkinter import ttk, filedialog, messagebox, scrolledtext, simpledialog
from datetime import datetime
import threading
import queue
import time
import logging
import traceback
import random

# Configure logging to both file and console
logging.basicConfig(
    level=logging.INFO,
    format='%(asctime)s - %(levelname)s - %(message)s',
    filename='mbox_manager.log',
    filemode='a'
)
logger = logging.getLogger('MboxManager')

# Add console handler for terminal output
console_handler = logging.StreamHandler(sys.stdout)
console_handler.setLevel(logging.INFO)
console_formatter = logging.Formatter('%(asctime)s - %(levelname)s - %(message)s')
console_handler.setFormatter(console_formatter)
logger.addHandler(console_handler)


class QueueHandler(logging.Handler):
    """
    A handler that puts log records into a queue for the main thread to process
    """

    def __init__(self, log_queue):
        super().__init__()
        self.log_queue = log_queue

    def emit(self, record):
        self.log_queue.put(record)


class MboxManagerApp:
    def __init__(self, root):
        self.root = root
        self.root.title("MBox Email Manager")
        self.root.geometry("1200x800")  # Increased height for bigger content area

        # Store loaded mbox data
        self.mbox = None
        self.emails = []
        self.filtered_emails = []
        self.emails_per_page = 100
        self.current_page = 0
        self.total_pages = 0
        self.loading_cancelled = False
        self.emails_loaded = 0
        self.total_emails = 0
        self.select_all_var = tk.BooleanVar(value=False)

        # Track selected emails across all pages
        self.selected_email_indices = set()

        # Create a queue for thread communication
        self.queue = queue.Queue()

        # Create log handler for UI
        self.log_queue = queue.Queue()
        self.log_handler = QueueHandler(self.log_queue)
        self.log_handler.setLevel(logging.INFO)
        logger.addHandler(self.log_handler)

        # Create dictionary to map tree items to email indices
        self.tree_item_to_email = {}

        # Track in-memory email IDs to prevent duplicates
        self.email_id_tracker = set()

        # Filter mode variables
        self.subject_filter_mode = tk.StringVar(value="contains")
        self.from_filter_mode = tk.StringVar(value="contains")
        self.to_filter_mode = tk.StringVar(value="contains")
        self.content_filter_mode = tk.StringVar(value="contains")  # Content filter mode

        # Setup main UI layout with panes for better space allocation
        self.create_widgets()
        self.setup_layout()

        # Start the periodic check for queue updates
        self.check_queue()
        self.check_log_queue()

    def create_widgets(self):
        # Top frame for file operations
        self.top_frame = ttk.Frame(self.root, padding="10")

        # File selection
        self.file_label = ttk.Label(self.top_frame, text="No file selected")
        self.browse_button = ttk.Button(self.top_frame, text="Browse", command=self.browse_file)
        self.cancel_button = ttk.Button(self.top_frame, text="Cancel Loading", command=self.cancel_loading,
                                        state=tk.DISABLED)

        # Action buttons - MOVED TO TOP
        self.remove_button = ttk.Button(self.top_frame, text="Remove Selected", command=self.remove_selected)
        self.export_button = ttk.Button(self.top_frame, text="Apply Changes", command=self.export_or_save_dialog)

        # Stats frame
        self.stats_frame = ttk.LabelFrame(self.root, text="Statistics", padding="10")
        self.stats_label = ttk.Label(self.stats_frame, text="No file loaded")

        # Filter frame
        self.filter_frame = ttk.LabelFrame(self.root, text="Filter Emails", padding="10")

        # Create a grid layout for filters
        self.filter_frame.columnconfigure(1, weight=1)
        self.filter_frame.columnconfigure(3, weight=1)

        # Subject filter
        self.subject_filter_label = ttk.Label(self.filter_frame, text="Subject:")
        self.subject_filter = ttk.Entry(self.filter_frame, width=30)
        self.subject_filter.bind("<KeyRelease>", self.apply_filters)

        # Subject filter mode
        self.subject_filter_mode_combobox = ttk.Combobox(self.filter_frame,
                                                         textvariable=self.subject_filter_mode,
                                                         values=["contains", "does not contain"],
                                                         width=15,
                                                         state="readonly")
        self.subject_filter_mode_combobox.bind("<<ComboboxSelected>>", self.apply_filters)

        # From filter
        self.from_filter_label = ttk.Label(self.filter_frame, text="From:")
        self.from_filter = ttk.Entry(self.filter_frame, width=30)
        self.from_filter.bind("<KeyRelease>", self.apply_filters)

        # From filter mode
        self.from_filter_mode_combobox = ttk.Combobox(self.filter_frame,
                                                      textvariable=self.from_filter_mode,
                                                      values=["contains", "does not contain"],
                                                      width=15,
                                                      state="readonly")
        self.from_filter_mode_combobox.bind("<<ComboboxSelected>>", self.apply_filters)

        # To filter
        self.to_filter_label = ttk.Label(self.filter_frame, text="To:")
        self.to_filter = ttk.Entry(self.filter_frame, width=30)
        self.to_filter.bind("<KeyRelease>", self.apply_filters)

        # To filter mode
        self.to_filter_mode_combobox = ttk.Combobox(self.filter_frame,
                                                    textvariable=self.to_filter_mode,
                                                    values=["contains", "does not contain"],
                                                    width=15,
                                                    state="readonly")
        self.to_filter_mode_combobox.bind("<<ComboboxSelected>>", self.apply_filters)

        # Date filter
        self.date_filter_label = ttk.Label(self.filter_frame, text="Date after (YYYY-MM-DD):")
        self.date_filter = ttk.Entry(self.filter_frame, width=15)
        self.date_filter.bind("<KeyRelease>", self.apply_filters)

        # Message content filter
        self.content_filter_label = ttk.Label(self.filter_frame, text="Message content (comma-separated):")
        self.content_filter = ttk.Entry(self.filter_frame, width=30)
        self.content_filter.bind("<KeyRelease>", self.apply_filters)

        # Content filter mode
        self.content_filter_mode_combobox = ttk.Combobox(self.filter_frame,
                                                         textvariable=self.content_filter_mode,
                                                         values=["contains", "does not contain"],
                                                         width=15,
                                                         state="readonly")
        self.content_filter_mode_combobox.bind("<<ComboboxSelected>>", self.apply_filters)

        # Clear filter button
        self.clear_filter_button = ttk.Button(self.filter_frame, text="Clear Filters", command=self.clear_filters)

        # Main content area - Two column layout with PanedWindow
        self.main_paned = ttk.PanedWindow(self.root, orient=tk.HORIZONTAL)

        # Left frame for email list
        self.list_frame = ttk.LabelFrame(self.main_paned, text="Email List")

        # Create frame for select all checkbox
        self.select_frame = ttk.Frame(self.list_frame)
        self.select_all_var = tk.BooleanVar(value=False)

        # Select all mode variable
        self.select_all_mode = tk.StringVar(value="current page")

        # Create a frame for selection controls
        self.select_all_frame = ttk.Frame(self.select_frame)
        self.select_all_check = ttk.Checkbutton(
            self.select_all_frame,
            text="Select All",
            variable=self.select_all_var,
            command=self.toggle_select_all
        )

        # Select all mode combobox
        self.select_all_mode_combobox = ttk.Combobox(
            self.select_all_frame,
            textvariable=self.select_all_mode,
            values=["current page", "all pages"],
            width=15,
            state="readonly"
        )

        # Create treeview for emails with scrollbar
        self.tree_frame = ttk.Frame(self.list_frame)
        self.tree = ttk.Treeview(self.tree_frame, columns=("From", "To", "Subject", "Date"), show="headings")
        self.tree.heading("From", text="From")
        self.tree.heading("To", text="To")
        self.tree.heading("Subject", text="Subject")
        self.tree.heading("Date", text="Date")

        self.tree.column("From", width=150, minwidth=100)
        self.tree.column("To", width=150, minwidth=100)
        self.tree.column("Subject", width=250, minwidth=100)
        self.tree.column("Date", width=120, minwidth=80)

        # Bind selection event to display email content
        self.tree.bind('<<TreeviewSelect>>', self.display_email_content)

        # Create scrollbars for treeview
        self.tree_vscrollbar = ttk.Scrollbar(self.tree_frame, orient="vertical", command=self.tree.yview)
        self.tree.configure(yscrollcommand=self.tree_vscrollbar.set)
        self.tree_hscrollbar = ttk.Scrollbar(self.tree_frame, orient="horizontal", command=self.tree.xview)
        self.tree.configure(xscrollcommand=self.tree_hscrollbar.set)

        # Pagination frame
        self.pagination_frame = ttk.Frame(self.list_frame)
        self.prev_button = ttk.Button(self.pagination_frame, text="Previous", command=self.prev_page, state=tk.DISABLED)
        self.page_label = ttk.Label(self.pagination_frame, text="Page 0 of 0")
        self.next_button = ttk.Button(self.pagination_frame, text="Next", command=self.next_page, state=tk.DISABLED)
        self.jump_label = ttk.Label(self.pagination_frame, text="Jump to page:")
        self.jump_entry = ttk.Entry(self.pagination_frame, width=5)
        self.jump_button = ttk.Button(self.pagination_frame, text="Go", command=self.jump_to_page)

        # Right frame for email content
        self.content_frame = ttk.LabelFrame(self.main_paned, text="Email Content")

        # Email headers frame
        self.header_frame = ttk.Frame(self.content_frame)
        self.header_from = ttk.Label(self.header_frame, text="From: ", wraplength=600)
        self.header_to = ttk.Label(self.header_frame, text="To: ", wraplength=600)
        self.header_subject = ttk.Label(self.header_frame, text="Subject: ", wraplength=600)
        self.header_date = ttk.Label(self.header_frame, text="Date: ")

        # Email body text area with scrollbars
        self.email_text_frame = ttk.Frame(self.content_frame)
        self.email_text = scrolledtext.ScrolledText(self.email_text_frame, wrap=tk.WORD)
        self.email_text.config(state=tk.DISABLED)

        # Bottom frame for status and progress
        self.bottom_frame = ttk.Frame(self.root, padding="5")
        self.status_label = ttk.Label(self.bottom_frame, text="Ready")

        # Progress bar and percentage
        self.progress_frame = ttk.Frame(self.bottom_frame)
        self.progress = ttk.Progressbar(self.progress_frame, orient=tk.HORIZONTAL, length=300, mode='determinate')
        self.progress_percent = ttk.Label(self.progress_frame, text="0%")

    def setup_layout(self):
        # Configure root to make columns and rows expand properly
        self.root.columnconfigure(0, weight=1)
        self.root.rowconfigure(2, weight=1)  # Main content area will expand

        # Top frame layout - Now includes action buttons
        self.top_frame.pack(fill=tk.X, padx=10, pady=5)
        self.file_label.pack(side=tk.LEFT, padx=5)

        # Action buttons on the right side of top frame
        self.export_button.pack(side=tk.RIGHT, padx=5)
        self.remove_button.pack(side=tk.RIGHT, padx=5)
        self.browse_button.pack(side=tk.RIGHT, padx=5)
        self.cancel_button.pack(side=tk.RIGHT, padx=5)

        # Stats frame layout
        self.stats_frame.pack(fill=tk.X, padx=10, pady=5)
        self.stats_label.pack(side=tk.LEFT, padx=5)

        # Filter frame layout
        self.filter_frame.pack(fill=tk.X, padx=10, pady=5)

        # Place filters directly in the filter_frame using grid
        row = 0
        self.subject_filter_label.grid(row=row, column=0, padx=5, pady=5, sticky=tk.W)
        self.subject_filter.grid(row=row, column=1, padx=5, pady=5, sticky=tk.W + tk.E)
        self.subject_filter_mode_combobox.grid(row=row, column=2, padx=5, pady=5, sticky=tk.W)

        row += 1
        self.from_filter_label.grid(row=row, column=0, padx=5, pady=5, sticky=tk.W)
        self.from_filter.grid(row=row, column=1, padx=5, pady=5, sticky=tk.W + tk.E)
        self.from_filter_mode_combobox.grid(row=row, column=2, padx=5, pady=5, sticky=tk.W)

        row += 1
        self.to_filter_label.grid(row=row, column=0, padx=5, pady=5, sticky=tk.W)
        self.to_filter.grid(row=row, column=1, padx=5, pady=5, sticky=tk.W + tk.E)
        self.to_filter_mode_combobox.grid(row=row, column=2, padx=5, pady=5, sticky=tk.W)

        row += 1
        self.date_filter_label.grid(row=row, column=0, padx=5, pady=5, sticky=tk.W)
        self.date_filter.grid(row=row, column=1, padx=5, pady=5, sticky=tk.W)

        # Add content filter (with its own row)
        row += 1
        self.content_filter_label.grid(row=row, column=0, padx=5, pady=5, sticky=tk.W)
        self.content_filter.grid(row=row, column=1, padx=5, pady=5, sticky=tk.W + tk.E)
        self.content_filter_mode_combobox.grid(row=row, column=2, padx=5, pady=5, sticky=tk.W)

        # Clear filter button on the last row
        self.clear_filter_button.grid(row=row, column=3, padx=5, pady=5, sticky=tk.W)

        # Main paned window (two-column layout)
        self.main_paned.pack(fill=tk.BOTH, expand=True, padx=10, pady=5)

        # Add frames to main paned window
        self.main_paned.add(self.list_frame, weight=1)
        self.main_paned.add(self.content_frame, weight=2)  # Content gets more space

        # Configure frames to handle resizing
        for frame in (self.list_frame, self.content_frame):
            frame.columnconfigure(0, weight=1)
            frame.rowconfigure(2, weight=1)  # Main content in row 2

        # ---- Left side: Email list layout ----
        # Select all checkbox and mode selector
        self.select_frame.pack(fill=tk.X, pady=2)
        self.select_all_frame.pack(side=tk.LEFT, padx=5)
        self.select_all_check.pack(side=tk.LEFT, padx=5)
        ttk.Label(self.select_all_frame, text="on").pack(side=tk.LEFT, padx=2)
        self.select_all_mode_combobox.pack(side=tk.LEFT, padx=5)

        # Tree with scrollbars
        self.tree_frame.pack(fill=tk.BOTH, expand=True, padx=5, pady=5)
        self.tree_frame.columnconfigure(0, weight=1)
        self.tree_frame.rowconfigure(0, weight=1)

        self.tree.grid(row=0, column=0, sticky=tk.NSEW)
        self.tree_vscrollbar.grid(row=0, column=1, sticky=tk.NS)
        self.tree_hscrollbar.grid(row=1, column=0, sticky=tk.EW)

        # Pagination frame
        self.pagination_frame.pack(fill=tk.X, pady=5)
        self.prev_button.pack(side=tk.LEFT, padx=5)
        self.page_label.pack(side=tk.LEFT, padx=5)
        self.next_button.pack(side=tk.LEFT, padx=5)
        self.jump_button.pack(side=tk.RIGHT, padx=5)
        self.jump_entry.pack(side=tk.RIGHT, padx=5)
        self.jump_label.pack(side=tk.RIGHT, padx=5)

        # ---- Right side: Email content layout ----
        # Email headers
        self.header_frame.pack(fill=tk.X, pady=5, padx=5)
        self.header_from.pack(anchor=tk.W, pady=2, fill=tk.X)
        self.header_to.pack(anchor=tk.W, pady=2, fill=tk.X)
        self.header_subject.pack(anchor=tk.W, pady=2, fill=tk.X)
        self.header_date.pack(anchor=tk.W, pady=2, fill=tk.X)

        # Email body text
        self.email_text_frame.pack(fill=tk.BOTH, expand=True, padx=5, pady=5)
        self.email_text_frame.columnconfigure(0, weight=1)
        self.email_text_frame.rowconfigure(0, weight=1)
        self.email_text.pack(fill=tk.BOTH, expand=True)

        # Bottom frame layout - For status and progress
        self.bottom_frame.pack(fill=tk.X, padx=10, pady=5)
        self.status_label.pack(side=tk.LEFT, padx=5)

        # Progress bar and percentage
        self.progress_frame.pack(side=tk.LEFT, padx=20)
        self.progress.pack(side=tk.LEFT, padx=5)
        self.progress_percent.pack(side=tk.LEFT, padx=5)

        # Disable buttons initially
        self.remove_button.config(state=tk.DISABLED)
        self.export_button.config(state=tk.DISABLED)
        self.jump_button.config(state=tk.DISABLED)

    def browse_file(self):
        """Open file dialog to select an mbox file"""
        file_path = filedialog.askopenfilename(
            title="Select an mbox file",
            filetypes=[("MBox files", "*.mbox"), ("All files", "*.*")]
        )

        if file_path:
            # Get file size
            file_size_bytes = os.path.getsize(file_path)
            file_size_gb = file_size_bytes / (1024 ** 3)

            self.file_label.config(text=f"File: {os.path.basename(file_path)} ({file_size_gb:.2f} GB)")
            self.status_label.config(text="Preparing to load emails...")
            self.progress['value'] = 0
            self.progress_percent.config(text="0%")

            # Ask user how to load the file if it's very large
            if file_size_gb > 1:  # If file is larger than 1GB
                load_option = messagebox.askyesnocancel(
                    "Large File Detected",
                    f"This file is {file_size_gb:.2f} GB and may take a long time to process completely.\n\n"
                    f"Would you like to:\n"
                    f"- Yes: Load emails in a sampled mode (faster, loads every Nth email)\n"
                    f"- No: Load emails in regular mode (slower but complete)\n"
                    f"- Cancel: Abort loading"
                )

                if load_option is None:  # Cancel
                    self.status_label.config(text="Loading cancelled")
                    return

                if load_option:  # Yes - Use sampling
                    # For extremely large files, suggest a higher sampling rate
                    if file_size_gb > 10:
                        sampling_rate = simpledialog.askinteger(
                            "Sampling Rate",
                            f"Enter sampling rate (1 = all emails, 10 = every 10th email, etc).\n"
                            f"Recommended for {file_size_gb:.1f} GB: {max(10, int(file_size_gb * 5))}",
                            initialvalue=max(10, int(file_size_gb * 5)),
                            minvalue=1, maxvalue=10000
                        )
                        if sampling_rate is None:
                            self.status_label.config(text="Loading cancelled")
                            return
                    else:
                        sampling_rate = 10  # Default sampling rate for files 1-10GB

                    logger.info(
                        f"Loading file with sampling (every {sampling_rate}th email): {os.path.basename(file_path)}")
                else:  # No - Normal loading
                    sampling_rate = 1
                    logger.info(f"Loading file normally: {os.path.basename(file_path)}")
            else:
                # Small file, use regular loading
                sampling_rate = 1

            # Reset flags and data
            self.loading_cancelled = False
            self.emails_loaded = 0
            self.emails = []
            self.filtered_emails = []
            self.email_id_tracker.clear()
            self.selected_email_indices.clear()

            # Enable cancel button
            self.cancel_button.config(state=tk.NORMAL)

            # Log the action
            logger.info(f"Loading file: {os.path.basename(file_path)} ({file_size_gb:.2f} GB)")

            # Start a thread to load the mbox file
            loading_thread = threading.Thread(target=self.load_mbox, args=(file_path, sampling_rate))
            loading_thread.daemon = True
            loading_thread.start()

    def cancel_loading(self):
        """Cancel the loading process"""
        self.loading_cancelled = True
        self.status_label.config(text="Cancelling...")
        logger.info("Loading cancelled by user")

    def load_mbox(self, file_path, sampling_rate=1):
        """
        Load the mbox file in a separate thread, with sampling and pagination support

        Args:
            file_path: Path to the mbox file
            sampling_rate: Sample every Nth email (1 = all emails)
        """
        try:
            # First, try to estimate total emails using file size for very large files
            start_time = time.time()
            self.queue.put(('status', "Analyzing file..."))

            # Get file size in MB for estimation
            file_size_mb = os.path.getsize(file_path) / (1024 * 1024)
            file_size_gb = file_size_mb / 1024

            # Log file details
            logger.info(f"Processing file: {file_path}")
            logger.info(f"File size: {file_size_mb:.2f} MB ({file_size_gb:.2f} GB)")
            logger.info(f"Sampling rate: 1:{sampling_rate}")
            logger.info(f"Started processing at: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}")

            # For huge files, estimate based on file size instead of counting
            if file_size_mb > 1000:  # > 1GB
                # Very rough estimation: ~100KB per email on average
                # This varies greatly but gives us a starting point
                estimated_emails = int(file_size_mb * 10)  # 10 emails per MB is a rough estimate
                self.total_emails = estimated_emails
                logger.info(f"Estimated total emails based on file size: ~{estimated_emails:,}")
                self.queue.put(('status', f"Estimated ~{estimated_emails:,} emails, loading..."))
            else:
                try:
                    # Try to count emails for smaller files
                    self.queue.put(('status', "Counting emails..."))
                    self.mbox = mailbox.mbox(file_path)
                    self.total_emails = len(self.mbox)
                    logger.info(f"Total emails in mailbox: {self.total_emails:,}")
                    self.queue.put(('status', f"Found {self.total_emails:,} emails, loading..."))
                except Exception as e:
                    logger.warning(f"Error counting emails: {str(e)}")
                    # Fallback to estimation
                    estimated_emails = int(file_size_mb * 10)
                    self.total_emails = estimated_emails
                    self.queue.put(('status', f"Unable to count, estimated ~{estimated_emails:,} emails, loading..."))

            # Open the mbox file
            self.mbox = mailbox.mbox(file_path)

            # Initialize counts and storage
            self.emails = []
            self.emails_loaded = 0
            chunk_size = 1000  # Process in chunks for better responsiveness
            current_chunk = []
            last_progress_update = 0
            last_time_update = time.time()
            last_log_update = time.time()
            email_count = 0  # Counter for sampling

            # Terminal progress update frequency
            terminal_log_interval = 5  # seconds between terminal updates
            log_counter = 0  # For counting processed emails between logs

            # Get initial file position for tracking
            try:
                initial_file_pos = self.mbox._file.tell()
                total_file_size = os.path.getsize(file_path)
                logger.info(f"Initial file position: {initial_file_pos}, Total file size: {total_file_size}")
            except:
                initial_file_pos = 0
                total_file_size = os.path.getsize(file_path)
                logger.info(f"Could not get initial file position, using 0. Total file size: {total_file_size}")

            # Process the emails
            logger.info("Starting to process emails...")
            for i, message in enumerate(self.mbox):
                # Check if loading was cancelled
                if self.loading_cancelled:
                    logger.info(f"Loading cancelled after {self.emails_loaded:,} emails")
                    self.queue.put(('status', f"Loading cancelled after {self.emails_loaded:,} emails"))
                    break

                # Track raw processing count for terminal logs
                log_counter += 1

                # Apply sampling
                email_count += 1
                if sampling_rate > 1 and email_count % sampling_rate != 0:
                    continue  # Skip this email based on sampling rate

                # For extremely large files, consider random sampling instead of sequential
                if self.total_emails > 1000000 and sampling_rate > 100:
                    # Skip with high probability to get a random sample
                    if random.random() > 1.0 / sampling_rate:
                        continue

                # Extract email details
                try:
                    email_data = self.extract_email_data(message)

                    # Check for duplicates using message_id
                    message_id = email_data['message_id']
                    if message_id in self.email_id_tracker:
                        logger.debug(f"Skipping duplicate email with Message-ID: {message_id}")
                        continue
                    else:
                        self.email_id_tracker.add(message_id)

                    current_chunk.append(email_data)
                    self.emails_loaded += 1
                except Exception as e:
                    logger.error(f"Error processing email #{i}: {str(e)}")
                    continue

                # If early preview is enabled, start showing emails after a few are loaded
                if self.emails_loaded == 100 and len(self.emails) == 0:
                    # Add first batch to display some data quickly
                    self.emails.extend(current_chunk)
                    self.queue.put(('preview_emails', None))
                    logger.info("Showing email preview while continuing to load")

                # Process chunk when it reaches the chunk size
                if len(current_chunk) >= chunk_size:
                    self.emails.extend(current_chunk)
                    current_chunk = []

                # Update progress every 0.5 seconds to avoid UI freezing
                current_time = time.time()

                # Terminal log updates at set interval
                if (current_time - last_log_update) > terminal_log_interval:
                    try:
                        # Get current position in file
                        current_pos = self.mbox._file.tell()
                        pos_percent = min(100, int((current_pos / total_file_size) * 100))

                        # Calculate processing speed
                        emails_per_sec = log_counter / (current_time - last_log_update)

                        # Log to terminal
                        logger.info(
                            f"Processed: {log_counter:,} emails since last update "
                            f"({emails_per_sec:.1f} emails/sec), "
                            f"File position: {current_pos:,}/{total_file_size:,} bytes ({pos_percent}%)"
                        )

                        # Reset counter
                        log_counter = 0
                        last_log_update = current_time
                    except Exception as e:
                        logger.error(f"Error during terminal logging: {str(e)}")

                # Update GUI progress
                if (current_time - last_time_update) > 0.5:
                    # Calculate progress based on file position for huge files
                    if file_size_mb > 1000:
                        try:
                            # Try to get current position in file for better progress estimation
                            current_pos = self.mbox._file.tell()
                            progress_value = min(int((current_pos / total_file_size) * 100), 100)
                        except:
                            # Fallback to email count based progress
                            progress_value = min(int((self.emails_loaded / (self.total_emails / sampling_rate)) * 100),
                                                 100)
                    else:
                        # Normal progress calculation
                        progress_value = min(int((self.emails_loaded / (self.total_emails / sampling_rate)) * 100), 100)

                    # Only update if progress has changed
                    if progress_value != last_progress_update:
                        self.queue.put(('progress', progress_value))
                        last_progress_update = progress_value

                    # Update status with loading speed
                    elapsed = current_time - start_time
                    if elapsed > 0:
                        emails_per_second = self.emails_loaded / elapsed
                        if sampling_rate > 1:
                            status_text = (
                                f"Loaded {self.emails_loaded:,} emails (sampling 1:{sampling_rate}) "
                                f"at {emails_per_second:.1f} emails/sec"
                            )
                        else:
                            estimated_total_time = self.total_emails / emails_per_second if emails_per_second > 0 else 0
                            remaining_time = estimated_total_time - elapsed

                            status_text = (
                                f"Loaded {self.emails_loaded:,} of ~{self.total_emails:,} emails "
                                f"({emails_per_second:.1f} emails/sec, "
                                f"~{remaining_time / 60:.1f} min remaining)"
                            )

                        self.queue.put(('status', status_text))

                    last_time_update = current_time

            # Add any remaining emails in the last chunk
            if current_chunk:
                self.emails.extend(current_chunk)

            # Calculate total processing time
            total_time = time.time() - start_time

            # Final terminal log
            logger.info(f"Processing completed at: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}")
            logger.info(f"Total processing time: {total_time:.1f} seconds")

            if self.emails_loaded > 0:
                if sampling_rate > 1:
                    logger.info(f"Loaded {self.emails_loaded:,} emails with sampling rate 1:{sampling_rate} "
                                f"in {total_time:.1f} seconds ({self.emails_loaded / total_time:.1f} emails/sec)")
                else:
                    logger.info(f"Loaded {self.emails_loaded:,} emails in {total_time:.1f} seconds "
                                f"({self.emails_loaded / total_time:.1f} emails/sec)")

            # Set up pagination
            self.current_page = 0
            self.total_pages = max(1, (len(self.emails) + self.emails_per_page - 1) // self.emails_per_page)

            # Update the UI with the loaded emails
            self.queue.put(('display_emails', None))

            if sampling_rate > 1:
                self.queue.put(('status',
                                f"Loaded {self.emails_loaded:,} emails (sampling 1:{sampling_rate}) in {total_time:.1f} seconds"))
            else:
                self.queue.put(('status', f"Loaded {self.emails_loaded:,} emails in {total_time:.1f} seconds"))

            # Disable cancel button
            self.queue.put(('cancel_button_state', tk.DISABLED))

        except Exception as e:
            error_msg = f"Error loading file: {str(e)}"
            logger.error(error_msg)
            logger.error(traceback.format_exc())
            self.queue.put(('error', error_msg))
            self.queue.put(('cancel_button_state', tk.DISABLED))

    def extract_email_data(self, message):
        """Extract relevant data from email message"""
        # Extract From field
        from_field = message.get('From', '')
        # Extract To field
        to_field = message.get('To', '')
        # Extract Subject field
        subject = message.get('Subject', '')
        # Extract Date field
        date_str = message.get('Date', '')
        # Extract Message-ID field for duplicate detection
        message_id = message.get('Message-ID', '')

        # Try to parse the date
        date_obj = None
        try:
            date_obj = email.utils.parsedate_to_datetime(date_str)
            formatted_date = date_obj.strftime('%Y-%m-%d %H:%M')
        except:
            formatted_date = date_str

        # Clean and decode headers if needed
        try:
            subject = self.decode_header(subject)
            from_field = self.decode_header(from_field)
            to_field = self.decode_header(to_field)
        except Exception as e:
            logger.error(f"Error decoding headers: {str(e)}")

        # Generate a unique ID if no Message-ID is available
        if not message_id:
            # Create a pseudo-unique ID based on headers and content
            content_hash = hash(f"{from_field}|{to_field}|{subject}|{date_str}|{str(message.get_payload())[:100]}")
            message_id = f"generated-{content_hash}"

        # Extract message body for content searching
        body = self.extract_email_body(message)

        return {
            'message': message,
            'from': from_field,
            'to': to_field,
            'subject': subject,
            'date_str': date_str,
            'date_obj': date_obj,
            'formatted_date': formatted_date,
            'message_id': message_id,
            'body': body  # Store the body content for searching
        }

    def extract_email_body(self, message):
        """Extract the body content from an email message"""
        body = ""

        # Try to get plain text content first
        if message.is_multipart():
            for part in message.walk():
                content_type = part.get_content_type()
                content_disposition = str(part.get("Content-Disposition"))

                # Skip attachments
                if "attachment" in content_disposition:
                    continue

                # Get plain text or HTML content
                if content_type == "text/plain":
                    try:
                        body_part = part.get_payload(decode=True).decode(errors='replace')
                        body += body_part + "\n"
                    except Exception as e:
                        body += f"[Error decoding plain text content: {str(e)}]\n"
                elif content_type == "text/html" and not body:
                    # Only use HTML if we don't have plain text
                    try:
                        html_part = part.get_payload(decode=True).decode(errors='replace')
                        # Simple HTML stripping for search purposes
                        # This is basic and doesn't handle all HTML properly
                        body += re.sub(r'<[^>]+>', ' ', html_part)
                    except Exception as e:
                        pass
        else:
            # Not multipart - try to decode the payload
            try:
                body = message.get_payload(decode=True).decode(errors='replace')
            except Exception as e:
                try:
                    body = message.get_payload()
                except:
                    body = ""

        return body

    def decode_header(self, header):
        """Decode email header properly"""
        if not header:
            return ""

        try:
            # First try the email.header.decode_header method
            parts = email.header.decode_header(header)
            decoded_parts = []

            for part, encoding in parts:
                if isinstance(part, bytes):
                    # Try with the specified encoding
                    if encoding:
                        try:
                            decoded_parts.append(part.decode(encoding))
                        except (LookupError, UnicodeDecodeError):
                            # If that fails, try utf-8
                            try:
                                decoded_parts.append(part.decode('utf-8'))
                            except UnicodeDecodeError:
                                # Last resort, use latin-1 which will always work but might be incorrect
                                decoded_parts.append(part.decode('latin-1', errors='replace'))
                    else:
                        # No encoding specified, try utf-8
                        try:
                            decoded_parts.append(part.decode('utf-8'))
                        except UnicodeDecodeError:
                            # Fallback to latin-1
                            decoded_parts.append(part.decode('latin-1', errors='replace'))
                else:
                    # It's already a string
                    decoded_parts.append(part)

            return "".join(str(p) for p in decoded_parts)

        except Exception as e:
            # If all else fails, just return the header with replacement for invalid chars
            if isinstance(header, bytes):
                return header.decode('utf-8', errors='replace')
            return str(header)

    def check_queue(self):
        """Check for updates from the worker thread"""
        try:
            while True:
                action, data = self.queue.get_nowait()

                if action == 'progress':
                    self.progress['value'] = data
                    self.progress_percent.config(text=f"{data}%")
                elif action == 'display_emails':
                    self.filtered_emails = self.emails.copy()
                    self.update_email_list()
                    self.remove_button.config(state=tk.NORMAL)
                    self.export_button.config(state=tk.NORMAL)
                    self.jump_button.config(state=tk.NORMAL)

                    # Update stats
                    self.update_stats()
                elif action == 'preview_emails':
                    # Display first batch of emails while still loading
                    self.filtered_emails = self.emails.copy()
                    self.update_email_list()
                    self.remove_button.config(state=tk.NORMAL)
                    self.update_stats()
                    messagebox.showinfo("Preview Available",
                                        "Showing email preview while continuing to load the full file.")
                elif action == 'status':
                    self.status_label.config(text=data)
                elif action == 'error':
                    messagebox.showerror("Error", data)
                elif action == 'cancel_button_state':
                    self.cancel_button.config(state=data)
                elif action == 'success':
                    messagebox.showinfo("Success", data)

                self.queue.task_done()
        except queue.Empty:
            pass

        # Schedule to check again
        self.root.after(100, self.check_queue)

    def check_log_queue(self):
        """Check for new log messages"""
        try:
            while True:
                record = self.log_queue.get_nowait()
                formatter = logging.Formatter('%(asctime)s - %(levelname)s - %(message)s')
                log_message = formatter.format(record)
                # Log messages are printed to console but not displayed in UI anymore
                self.log_queue.task_done()
        except queue.Empty:
            pass

        # Schedule to check again
        self.root.after(100, self.check_log_queue)

    def clear_log(self):
        """Clear the log (kept for compatibility)"""
        pass

    def update_stats(self):
        """Update the statistics display"""
        if self.emails:
            stats_text = (
                f"Total emails: {len(self.emails):,} | "
                f"Filtered: {len(self.filtered_emails):,} | "
                f"Pages: {self.total_pages:,} | "
                f"Emails per page: {self.emails_per_page}"
            )
            self.stats_label.config(text=stats_text)

    def toggle_select_all(self):
        """Toggle select all emails in the current page or all pages"""
        mode = self.select_all_mode.get()

        if self.select_all_var.get():
            if mode == "current page":
                # Select all visible items
                for item in self.tree.get_children():
                    self.tree.selection_add(item)
                    # Add to our global tracking set
                    if item in self.tree_item_to_email:
                        self.selected_email_indices.add(self.tree_item_to_email[item])
            else:  # all pages
                # Select all emails in the filtered set
                self.selected_email_indices = set(range(len(self.filtered_emails)))

                # Also select visible items in the current view
                for item in self.tree.get_children():
                    self.tree.selection_add(item)

                # Update status to show how many selected
                self.status_label.config(
                    text=f"Selected all {len(self.selected_email_indices):,} emails across all pages")
        else:
            # Deselect all items
            self.tree.selection_remove(self.tree.get_children())

            if mode == "all pages":
                # Clear global selection set
                self.selected_email_indices.clear()
                self.status_label.config(text="Cleared all selections")

    def prev_page(self):
        """Go to the previous page"""
        if self.current_page > 0:
            self.current_page -= 1
            self.update_email_list()
            self.select_all_var.set(False)

    def next_page(self):
        """Go to the next page"""
        if self.current_page < self.total_pages - 1:
            self.current_page += 1
            self.update_email_list()
            self.select_all_var.set(False)

    def jump_to_page(self):
        """Jump to a specific page"""
        try:
            page = int(self.jump_entry.get())
            if 1 <= page <= self.total_pages:
                self.current_page = page - 1
                self.update_email_list()
                self.select_all_var.set(False)
            else:
                messagebox.showinfo("Invalid Page", f"Please enter a page number between 1 and {self.total_pages}")
        except ValueError:
            messagebox.showinfo("Invalid Input", "Please enter a valid page number")

    def update_email_list(self):
        """Update the email list treeview with pagination"""
        # Clear existing items
        for item in self.tree.get_children():
            self.tree.delete(item)

        # Clear the mapping dictionary
        self.tree_item_to_email = {}

        if not self.filtered_emails:
            self.page_label.config(text="Page 0 of 0")
            self.prev_button.config(state=tk.DISABLED)
            self.next_button.config(state=tk.DISABLED)

            # Clear email content display
            self.header_from.config(text="From: ")
            self.header_to.config(text="To: ")
            self.header_subject.config(text="Subject: ")
            self.header_date.config(text="Date: ")
            self.email_text.config(state=tk.NORMAL)
            self.email_text.delete(1.0, tk.END)
            self.email_text.config(state=tk.DISABLED)
            return

        # Calculate start and end indices for current page
        start_idx = self.current_page * self.emails_per_page
        end_idx = min(start_idx + self.emails_per_page, len(self.filtered_emails))

        # Add the filtered emails for the current page to the treeview
        for i, email_data in enumerate(self.filtered_emails[start_idx:end_idx]):
            actual_idx = start_idx + i
            item_id = self.tree.insert('', tk.END, values=(
                email_data['from'],
                email_data['to'],
                email_data['subject'],
                email_data['formatted_date']
            ))
            # Store the mapping from tree item to email index in filtered_emails
            self.tree_item_to_email[item_id] = actual_idx

            # If this email is in our selected set, make sure it appears selected
            if actual_idx in self.selected_email_indices:
                self.tree.selection_add(item_id)

        # Update pagination controls
        self.page_label.config(text=f"Page {self.current_page + 1} of {self.total_pages}")

        # Enable/disable pagination buttons
        self.prev_button.config(state=tk.NORMAL if self.current_page > 0 else tk.DISABLED)
        self.next_button.config(state=tk.NORMAL if self.current_page < self.total_pages - 1 else tk.DISABLED)

        # Update selection status
        if self.selected_email_indices:
            self.status_label.config(text=f"Selected {len(self.selected_email_indices):,} emails across all pages")

    def display_email_content(self, event):
        """Display the content of the selected email"""
        selected_items = self.tree.selection()
        if not selected_items:
            return

        # Get the first selected item
        selected_item = selected_items[0]

        # Get the email index from our mapping dictionary
        if selected_item in self.tree_item_to_email:
            actual_index = self.tree_item_to_email[selected_item]

            # Store this selection in our global tracking set
            self.selected_email_indices.add(actual_index)

            if 0 <= actual_index < len(self.filtered_emails):
                # Get the email data
                email_data = self.filtered_emails[actual_index]

                # Update headers
                self.header_from.config(text=f"From: {email_data['from']}")
                self.header_to.config(text=f"To: {email_data['to']}")
                self.header_subject.config(text=f"Subject: {email_data['subject']}")
                self.header_date.config(text=f"Date: {email_data['formatted_date']}")

                # Add the message ID for debugging if available
                message_id = email_data.get('message_id', '')
                if message_id:
                    message_id_text = f"Message-ID: {message_id[:50]}{'...' if len(message_id) > 50 else ''}"
                    logger.debug(message_id_text)

                # Get the email message
                message = email_data['message']

                # Extract body content
                body = ""

                # Try to get plain text content first
                if message.is_multipart():
                    for part in message.walk():
                        content_type = part.get_content_type()
                        content_disposition = str(part.get("Content-Disposition"))

                        # Skip attachments
                        if "attachment" in content_disposition:
                            continue

                        # Get plain text or HTML content
                        if content_type == "text/plain":
                            try:
                                body_part = part.get_payload(decode=True).decode(errors='replace')
                                body += body_part + "\n"
                            except Exception as e:
                                body += f"[Error decoding plain text content: {str(e)}]\n"
                        elif content_type == "text/html" and not body:
                            # Only use HTML if we don't have plain text
                            try:
                                html_part = part.get_payload(decode=True).decode(errors='replace')
                                body += f"[HTML Content Available - Showing raw HTML]\n{html_part}\n"
                            except Exception as e:
                                body += f"[Error decoding HTML content: {str(e)}]\n"
                else:
                    # Not multipart - try to decode the payload
                    try:
                        body = message.get_payload(decode=True).decode(errors='replace')
                    except Exception as e:
                        body = f"[Error decoding message content: {str(e)}]"

                        # Fallback to non-decoded content
                        try:
                            body = message.get_payload()
                        except:
                            body = "[Could not retrieve message content]"

                # If no body found, show a message
                if not body:
                    body = "[No readable content found in this email]"

                # Update the email text widget
                self.email_text.config(state=tk.NORMAL)
                self.email_text.delete(1.0, tk.END)
                self.email_text.insert(tk.END, body)
                self.email_text.config(state=tk.DISABLED)
        else:
            # Clear the content if no valid email selected
            self.header_from.config(text="From: ")
            self.header_to.config(text="To: ")
            self.header_subject.config(text="Subject: ")
            self.header_date.config(text="Date: ")

            self.email_text.config(state=tk.NORMAL)
            self.email_text.delete(1.0, tk.END)
            self.email_text.insert(tk.END, "No email selected")
            self.email_text.config(state=tk.DISABLED)

    def apply_filters(self, event=None):
        """Apply filters to the email list with support for 'does not contain' mode"""
        if not self.emails:
            return

        subject_filter = self.subject_filter.get().lower()
        from_filter = self.from_filter.get().lower()
        to_filter = self.to_filter.get().lower()
        date_filter = self.date_filter.get()
        content_filter = self.content_filter.get().lower()  # Content filter

        # Get filter modes
        subject_mode = self.subject_filter_mode.get()
        from_mode = self.from_filter_mode.get()
        to_mode = self.to_filter_mode.get()
        content_mode = self.content_filter_mode.get()  # Content filter mode

        # Parse date filter if present
        date_obj = None
        if date_filter:
            try:
                date_obj = datetime.strptime(date_filter, '%Y-%m-%d')
            except ValueError:
                pass

        # Process content filter words (comma-separated)
        content_words = []
        if content_filter:
            content_words = [word.strip() for word in content_filter.split(',')]
            content_words = [word for word in content_words if word]  # Remove empty strings

        # Log filter application
        logger.info(f"Applying filters: Subject[{subject_mode}]='{subject_filter}', "
                    f"From[{from_mode}]='{from_filter}', "
                    f"To[{to_mode}]='{to_filter}', "
                    f"Content[{content_mode}]='{content_filter}', "
                    f"Date after='{date_filter}'")

        # Apply filters
        start_time = time.time()
        self.filtered_emails = []
        filter_count = 0

        # Clear selection tracking when filters change
        self.selected_email_indices.clear()

        for email_data in self.emails:
            # Subject filter
            if subject_filter:
                subject_contains = subject_filter in email_data['subject'].lower()
                if ((subject_mode == "contains" and not subject_contains) or
                        (subject_mode == "does not contain" and subject_contains)):
                    continue

            # From filter
            if from_filter:
                from_contains = from_filter in email_data['from'].lower()
                if ((from_mode == "contains" and not from_contains) or
                        (from_mode == "does not contain" and from_contains)):
                    continue

            # To filter
            if to_filter:
                to_contains = to_filter in email_data['to'].lower()
                if ((to_mode == "contains" and not to_contains) or
                        (to_mode == "does not contain" and to_contains)):
                    continue

            # Date filter - no "does not contain" option for dates
            if date_obj and email_data['date_obj'] and email_data['date_obj'] < date_obj:
                continue

            # Content filter (comma-separated words)
            if content_words:
                body_lower = email_data.get('body', '').lower()
                if content_mode == "contains":
                    # All words must be found in the content
                    if not all(word in body_lower for word in content_words):
                        continue
                else:  # "does not contain"
                    # None of the words should be in the content
                    if any(word in body_lower for word in content_words):
                        continue

            self.filtered_emails.append(email_data)
            filter_count += 1

        # Reset pagination for new filter
        self.current_page = 0
        self.total_pages = max(1, (len(self.filtered_emails) + self.emails_per_page - 1) // self.emails_per_page)
        self.select_all_var.set(False)

        # Update the display
        self.update_email_list()
        self.update_stats()

        filter_time = time.time() - start_time
        logger.info(f"Filter applied in {filter_time:.2f}s: {filter_count:,} emails matched")
        self.status_label.config(text=f"Showing {len(self.filtered_emails):,} emails (filtered in {filter_time:.2f}s)")

    def clear_filters(self):
        """Clear all filters"""
        self.subject_filter.delete(0, tk.END)
        self.from_filter.delete(0, tk.END)
        self.to_filter.delete(0, tk.END)
        self.date_filter.delete(0, tk.END)
        self.content_filter.delete(0, tk.END)  # Clear content filter

        # Reset filter modes to default
        self.subject_filter_mode.set("contains")
        self.from_filter_mode.set("contains")
        self.to_filter_mode.set("contains")
        self.content_filter_mode.set("contains")  # Reset content filter mode

        logger.info("Filters cleared")

        if self.emails:
            self.filtered_emails = self.emails.copy()

            # Reset pagination
            self.current_page = 0
            self.total_pages = max(1, (len(self.filtered_emails) + self.emails_per_page - 1) // self.emails_per_page)
            self.select_all_var.set(False)

            self.update_email_list()
            self.update_stats()
            self.status_label.config(text=f"Showing all {len(self.filtered_emails):,} emails")

    def remove_selected(self):
        """Remove selected emails from the list"""
        # If we have global selections across all pages, use those
        if self.select_all_mode.get() == "all pages" and self.selected_email_indices:
            # Calculate which emails to remove
            to_remove = list(self.selected_email_indices)
            to_remove.sort(reverse=True)  # Sort in reverse for safe removal

            removed_count = 0
            # Remove emails from filtered_emails
            for idx in to_remove:
                if 0 <= idx < len(self.filtered_emails):
                    email_to_remove = self.filtered_emails[idx]

                    # Also remove from the main emails list if present
                    if email_to_remove in self.emails:
                        self.emails.remove(email_to_remove)

                    # Remove from filtered list
                    del self.filtered_emails[idx]
                    removed_count += 1

            # Clear the selection tracking set
            self.selected_email_indices.clear()
        else:
            # Just process selected items on the current page
            selected_items = self.tree.selection()
            if not selected_items:
                messagebox.showinfo("Info", "No emails selected")
                return

            # Get the indices of the selected items from our mapping
            selected_indices = []
            for item in selected_items:
                if item in self.tree_item_to_email:
                    idx = self.tree_item_to_email[item]
                    selected_indices.append(idx)
                    # Also remove from our global selection set if present
                    if idx in self.selected_email_indices:
                        self.selected_email_indices.remove(idx)

            # Sort in reverse order to avoid index issues when removing
            selected_indices.sort(reverse=True)

            # Remove emails from filtered_emails
            removed_count = 0
            for idx in selected_indices:
                if 0 <= idx < len(self.filtered_emails):
                    # Also remove from the main emails list if present
                    email_to_remove = self.filtered_emails[idx]
                    if email_to_remove in self.emails:
                        self.emails.remove(email_to_remove)

                    del self.filtered_emails[idx]
                    removed_count += 1

        # Recalculate pagination
        self.total_pages = max(1, (len(self.filtered_emails) + self.emails_per_page - 1) // self.emails_per_page)
        if self.current_page >= self.total_pages and self.current_page > 0:
            self.current_page = self.total_pages - 1

        # Update the email list
        self.update_email_list()
        self.update_stats()

        logger.info(f"Removed {removed_count} emails")
        self.status_label.config(text=f"Removed {removed_count} emails. Showing {len(self.filtered_emails):,} emails")

        # Reset select all checkbox
        self.select_all_var.set(False)

    def export_or_save_dialog(self):
        """Show dialog to choose between modifying original file or creating a new one"""
        if not self.filtered_emails or not self.mbox:
            messagebox.showinfo("Info", "No emails to export")
            return

        # Get the original file path
        original_file_path = self.mbox._path

        # Ask if user wants to modify original or create new file
        option = messagebox.askyesnocancel(
            "Apply Changes",
            f"How would you like to apply your changes?\n\n"
            f"- Yes: Modify the original file ({os.path.basename(original_file_path)})\n"
            f"- No: Export to a new file\n"
            f"- Cancel: Do nothing",
            icon=messagebox.QUESTION
        )

        if option is None:  # Cancel
            return
        elif option:  # Yes - modify original
            self.export_remaining()
        else:  # No - create new file
            self.export_to_new_file()

    def export_to_new_file(self):
        """Export filtered emails to a new mbox file"""
        if not self.filtered_emails or not self.mbox:
            messagebox.showinfo("Info", "No emails to export")
            return

        # Get the original file path for default name suggestion
        original_file_path = self.mbox._path
        original_file_name = os.path.basename(original_file_path)
        base_name, ext = os.path.splitext(original_file_name)
        default_name = f"{base_name}_filtered{ext}"

        # Ask for new file path
        new_file_path = filedialog.asksaveasfilename(
            title="Save filtered emails as",
            initialfile=default_name,
            defaultextension=".mbox",
            filetypes=[("MBox files", "*.mbox"), ("All files", "*.*")]
        )

        if not new_file_path:
            return

        # Start a thread to export the emails
        self.status_label.config(text="Exporting to new file...")
        self.progress['value'] = 0
        self.progress_percent.config(text="0%")

        export_thread = threading.Thread(target=self.export_to_new_file_worker, args=(new_file_path,))
        export_thread.daemon = True
        export_thread.start()

    def export_to_new_file_worker(self, new_file_path):
        """Worker thread to export filtered emails to a new file"""
        try:
            # Create a new mbox file
            new_mbox = mailbox.mbox(new_file_path)
            new_mbox.clear()

            total_emails = len(self.filtered_emails)
            start_time = time.time()
            last_update_time = start_time

            logger.info(f"Exporting {total_emails:,} emails to new file: {new_file_path}")
            logger.info(f"Export started at: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}")

            for i, email_data in enumerate(self.filtered_emails):
                # Add the message to the new mbox
                new_mbox.add(email_data['message'])

                # Update progress every 100 emails or 0.5 seconds
                current_time = time.time()
                if i % 100 == 0 or (current_time - last_update_time) > 0.5:
                    progress_value = min(int((i + 1) / total_emails * 100), 100)
                    self.queue.put(('progress', progress_value))

                    # Update status with processing speed
                    if (current_time - start_time) > 0:
                        emails_per_second = (i + 1) / (current_time - start_time)
                        status_text = (
                            f"Exported {i + 1:,} of {total_emails:,} emails "
                            f"({emails_per_second:.1f} emails/sec)"
                        )
                        self.queue.put(('status', status_text))

                    last_update_time = current_time

            # Flush changes to disk
            new_mbox.flush()
            new_mbox.close()

            export_time = time.time() - start_time
            result_msg = f"Exported {total_emails:,} emails to {os.path.basename(new_file_path)} in {export_time:.1f}s"
            logger.info(result_msg)
            logger.info(f"Export completed at: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}")
            self.queue.put(('status', result_msg))
            self.queue.put(('progress', 100))

            # Show a success message
            self.queue.put(
                ('success', f"Successfully exported {total_emails:,} emails to {os.path.basename(new_file_path)}"))

        except Exception as e:
            error_msg = f"Error exporting to new file: {str(e)}"
            logger.error(error_msg)
            logger.error(traceback.format_exc())
            self.queue.put(('error', error_msg))
            self.queue.put(('status', "Export failed"))

    def export_remaining(self):
        """Edit the original mbox file to keep only the filtered emails"""
        if not self.filtered_emails or not self.mbox:
            messagebox.showinfo("Info", "No emails to export")
            return

        # Get the original file path
        original_file_path = self.mbox._path

        # Confirm with the user that they want to modify the original file
        result = messagebox.askokcancel(
            "Confirm Modification",
            f"This will modify your original mbox file:\n{original_file_path}\n\n"
            f"Only the {len(self.filtered_emails):,} currently filtered emails will be kept.\n"
            f"This operation cannot be undone. Continue?",
            icon=messagebox.WARNING
        )

        if not result:
            return

        # Offer to create a backup
        backup_result = messagebox.askyesno(
            "Create Backup",
            f"Would you like to create a backup of your original file before modifying it?",
            icon=messagebox.QUESTION
        )

        if backup_result:
            backup_path = filedialog.asksaveasfilename(
                title="Save backup as",
                initialfile=os.path.basename(original_file_path) + ".backup",
                defaultextension=".backup",
                filetypes=[("Backup files", "*.backup"), ("All files", "*.*")]
            )

            if backup_path:
                # Create backup
                self.status_label.config(text="Creating backup...")
                self.progress['value'] = 0
                self.progress_percent.config(text="0%")

                try:
                    # Simple file copy for backup
                    with open(original_file_path, 'rb') as src, open(backup_path, 'wb') as dst:
                        # Get file size for progress tracking
                        file_size = os.path.getsize(original_file_path)
                        bytes_copied = 0
                        buffer_size = 1024 * 1024  # 1MB buffer

                        while True:
                            buffer = src.read(buffer_size)
                            if not buffer:
                                break

                            dst.write(buffer)
                            bytes_copied += len(buffer)

                            # Update progress
                            progress = min(int((bytes_copied / file_size) * 100), 100)
                            self.progress['value'] = progress
                            self.progress_percent.config(text=f"{progress}%")
                            self.root.update_idletasks()  # Force UI update

                    logger.info(f"Created backup at: {backup_path}")
                    self.status_label.config(text=f"Backup created at {os.path.basename(backup_path)}")
                except Exception as e:
                    error_msg = f"Error creating backup: {str(e)}"
                    logger.error(error_msg)
                    messagebox.showerror("Backup Error", error_msg)
                    return

        # Proceed with modifying the original file
        self.status_label.config(text="Modifying original mbox file...")
        self.progress['value'] = 0
        self.progress_percent.config(text="0%")

        # Start a thread to modify the mbox file
        modify_thread = threading.Thread(target=self.modify_original_mbox, args=(original_file_path,))
        modify_thread.daemon = True
        modify_thread.start()

    def modify_original_mbox(self, file_path):
        """Modify the original mbox file to keep only the filtered emails"""
        try:
            # Create a temporary file
            temp_file_path = file_path + ".temp"

            # Create a new mbox file
            temp_mbox = mailbox.mbox(temp_file_path)
            temp_mbox.clear()

            total_emails = len(self.filtered_emails)
            start_time = time.time()
            last_update_time = start_time
            last_log_update = start_time
            log_counter = 0

            logger.info(f"Starting to modify original mbox file: {file_path}")
            logger.info(f"Keeping {total_emails:,} emails")
            logger.info(f"Modification started at: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}")

            for i, email_data in enumerate(self.filtered_emails):
                # Add the message to the temp mbox
                temp_mbox.add(email_data['message'])

                # Count for terminal logging
                log_counter += 1

                # Update progress every 0.5 seconds
                current_time = time.time()

                # Terminal log updates every 5 seconds
                if (current_time - last_log_update) > 5:
                    elapsed = current_time - last_log_update
                    emails_per_sec = log_counter / elapsed if elapsed > 0 else 0

                    # Log to terminal
                    logger.info(
                        f"Processed: {log_counter:,} emails since last update "
                        f"({emails_per_sec:.1f} emails/sec), "
                        f"Progress: {i + 1:,}/{total_emails:,} ({min(100, int((i + 1) / total_emails * 100))}%)"
                    )

                    # Reset counter
                    log_counter = 0
                    last_log_update = current_time

                # Update GUI progress
                if i % 100 == 0 or (current_time - last_update_time) > 0.5:
                    progress_value = min(int((i + 1) / total_emails * 100), 100)
                    self.queue.put(('progress', progress_value))

                    # Update status with processing speed
                    if (current_time - start_time) > 0:
                        emails_per_second = (i + 1) / (current_time - start_time)
                        estimated_total_time = total_emails / emails_per_second if emails_per_second > 0 else 0
                        remaining_time = estimated_total_time - (current_time - start_time)

                        status_text = (
                            f"Processed {i + 1:,} of {total_emails:,} emails "
                            f"({emails_per_second:.1f} emails/sec, "
                            f"~{remaining_time / 60:.1f} min remaining)"
                        )
                        self.queue.put(('status', status_text))

                    last_update_time = current_time

            # Flush changes to disk
            temp_mbox.flush()
            temp_mbox.close()

            # Close the original mbox file
            self.mbox.close()

            # Replace the original file with the temp file
            self.queue.put(('status', "Replacing original file..."))

            try:
                # On Windows, we need to remove the original file first
                if os.name == 'nt' and os.path.exists(file_path):
                    os.remove(file_path)

                os.rename(temp_file_path, file_path)

                # Reopen the modified file
                self.mbox = mailbox.mbox(file_path)

                modification_time = time.time() - start_time
                result_msg = f"Modified original mbox file to keep {total_emails:,} emails in {modification_time:.1f}s"
                logger.info(result_msg)
                logger.info(f"Modification completed at: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}")
                logger.info(f"Average processing speed: {total_emails / modification_time:.1f} emails/sec")
                self.queue.put(('status', result_msg))
                self.queue.put(('success', f"Successfully modified original file to keep {total_emails:,} emails"))

                # Update the stored emails to match what's now in the file
                self.emails = self.filtered_emails.copy()
                self.update_stats()

            except Exception as e:
                error_msg = f"Error replacing original file: {str(e)}"
                logger.error(error_msg)
                logger.error(traceback.format_exc())
                self.queue.put(('error', error_msg))
                self.queue.put(('status', f"Error: Original file unchanged, temp file at {temp_file_path}"))

        except Exception as e:
            error_msg = f"Error modifying original file: {str(e)}"
            logger.error(error_msg)
            logger.error(traceback.format_exc())
            self.queue.put(('error', error_msg))
            self.queue.put(('status', "Modification failed"))


def main():
    root = tk.Tk()
    app = MboxManagerApp(root)

    # Center window on screen
    window_width = 1200
    window_height = 800
    screen_width = root.winfo_screenwidth()
    screen_height = root.winfo_screenheight()
    center_x = int(screen_width / 2 - window_width / 2)
    center_y = int(screen_height / 2 - window_height / 2)
    root.geometry(f'{window_width}x{window_height}+{center_x}+{center_y}')

    # Set minimum window size
    root.minsize(1000, 700)

    # Add a nice theme if available
    try:
        style = ttk.Style()
        available_themes = style.theme_names()
        if 'clam' in available_themes:
            style.theme_use('clam')
        elif 'vista' in available_themes:
            style.theme_use('vista')
    except Exception:
        pass  # If theme setting fails, continue with default

    # Log application start
    logger.info("MBox Email Manager started")

    try:
        root.mainloop()
    except Exception as e:
        logger.error(f"Unhandled exception: {str(e)}")
        logger.error(traceback.format_exc())
        messagebox.showerror("Error", f"An unexpected error occurred: {str(e)}")


if __name__ == "__main__":
    main()