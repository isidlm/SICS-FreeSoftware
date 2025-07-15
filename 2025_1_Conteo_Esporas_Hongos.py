#                                                           #
# Aplicación interactiva para el conteo automático de esporas,
# células, nanoestructuras o microestructuras en imágenes   #
# microscópicas, con herramientas de procesamiento de imagen#
# y ajustes personalizados para mejorar la detección y      #
# segmentación de objetos circulares o irregulares.         #    
#                                                           #
# Universidad Autónoma de Occidente (UAdeO). Los Mochis, Sinaloa, Mex.
# Grupo de investigación en nanomateriales                  #
#                                                           # 
# Versión 10.07, 20250523_162313                            #
#                                                           #
#***********************************************************#**************************************************#
import os                                                   # Manejo de archivos y directorios
import tkinter as tk                                        # Interfaz gráfica
import numpy as np                                          # Manejo de arreglos y matrices
from tkinter import filedialog, messagebox                  # Funciones para abrir diálogos de archivos y mensajes
from tkinter import ttk                                     # Estilos y widgets adicionales
from tkinter import colorchooser                            # Diálogos para seleccionar colores
from tkinter import Menu                                    # Clase para crear menús 
from tkinter import Canvas                                  # Clase para crear lienzos
from tkinter import Label, Entry, Button                    # Widgets de etiquetas, campos de entrada y botones
from tkinter import Scrollbar, Frame                        # Widgets de barra de desplazamiento y marcos
from tkinter import OptionMenu, LabelFrame                  # Widgets de menús desplegables y recuadros con etiquetas
from tkinter import HORIZONTAL, VERTICAL                    # Constantes para orientaciones
from tkinter import RAISED, FLAT, SUNKEN, GROOVE, RIDGE     # Estilos de borde para botones
from tkinter import LEFT, RIGHT, TOP, BOTTOM, BOTH, X, Y    # Constantes de alineación
from tkinter import NW, N, E, W, NE, SE, SW, S, CENTER      # Constantes de alineación específica
from tkinter import NORMAL, DISABLED, ACTIVE                # Constantes para los estados de los widgets
from tkinter import END, INSERT, SEL_FIRST, SEL_LAST, SEL   # Constantes para manipular el cursor y selección
from tkinter import Scale                                   # Clase para crear deslizadores
from PIL import Image, ImageTk                              # Manejo de imágenes
import cv2                                                  # OpenCV para el procesamiento de imágenes
import matplotlib.pyplot as plt                             # Librería para graficar
from matplotlib.backends.backend_tkagg import FigureCanvasTkAgg # Clase para mostrar la gráfica en tkinter
from math import sqrt                                       # Función para calcular la raíz cuadrada
import math                                                 # Funciones matemáticas
from statistics import mean, median, stdev                  # Funciones estadísticas
import io                                                   # Entrada/Salida de datos
import time                                                 # Funciones para medir el tiempo
import inspect                                              # Inspección de objetos y funciones
#***********************************************************#**************************************#
# Variables globales para las coordenadas y la línea actual #
Ancho_img = 600                                             # Ancho de la imagen
Alto_img = 400                                              # Alto de la imagen 
BASE_WIDTH = 800                                            # Ancho base de la ventana
BASE_HEIGHT = 600                                           # Altura base de la ventana
BASE_WIDTH_max = 1024                                       # Ancho máximo de la ventana
BASE_HEIGHT_max = 768                                       # Altura máxima de la ventana
#                                                           #
####################################################################################################
#                                                           #
class Ventana_Usuario_v5_05(tk.Tk):                         # Clase para la ventana principal
    def __init__(self):                                     # Constructor de la clase Ventana_Usuario_v5_05
        super().__init__()                                  # Inicializar la clase madre
        # --------------------------------------------------#
        # Configuración principal de la ventana             #
        self.title("SICS: Scientific Image Counting System")     # Título de la ventana
        self.geometry(f"{BASE_WIDTH}x{BASE_HEIGHT}")        # Tamaño de la ventana
        self.protocol("WM_DELETE_WINDOW", self.on_closing)  # Capturar el evento de cierre de la ventana
        #                                                   #
        # --------------------------------------------------#
        # Configuración de imágenes                         #
        self.image_directory = None                         # Directorio de las imágenes
        self.current_image_path = None                      # Ruta de la imagen actual
        self.original_image = None                          # Imagen original sin cambios
        self.resized_image = None                           # Imagen redimensionada
        self.image_refs = []                                # Referencias de las imágenes
        self.image_labels = []                              # Etiquetas de las miniaturas
        self.img_tk = None                                  # Imagen en formato Tkinter
        self.temp_image = None                              # Imagen temporal procesada
        self.temp_image_name = ""                           # Nombre de la imagen temporal
        #                                                   #
        # --------------------------------------------------#
        # Zoom y escala                                     #        
        self.scale_factor = 1.0                             # Zoom actual
        self.min_scale = 0.1                                # Zoom mínimo permitido
        self.max_scale = 5.0                                # Zoom máximo permitido
        #                                                   #
        # Control de arrastre                               #
        self.last_x = 0                                     # Posición X del mouse antes del arrastre
        self.last_y = 0                                     # Posición Y del mouse antes del arrastre
        self.x_offset = 0                                   # centrado
        self.y_offset = 0                                   # centrado
        #                                                   #
        # --------------------------------------------------#
        # Gestión de estado y acciones                      #
        self.is_loading = False                             # Evitar cargas múltiples
        self.image_history = []                             # Historial de cambios
        self.just_undone = False                            # Evitar acciones múltiples
        self.undo_stack = []                                # Cambios realizados
        self.redo_stack = []                                # Cambios deshechos
        self.slider_repeat_job = None                       # Trabajo repetido del slider
        #                                                   #
        # --------------------------------------------------#
        # Configuración de la tabla de datos                #
        self.table_data = {"Número": [], "Conteo": []}      # Datos de la tabla
        self.selected_row = None                            # Fila seleccionada
        self.selected_row_index = None                      # Índice de la fila seleccionada
        self.agregar_a_tabla = False                        # Bandera para agregar a la tabla
        #                                                   #
        # --------------------------------------------------#
        # Variables de medición y dibujo                    #
        self.lines_drawn = []                               # Líneas dibujadas
        self.selected_line = None                           # Línea seleccionada
        self.start_x = self.start_y = 0                     # Coordenadas iniciales
        self.end_x = self.end_y = 0                         # Coordenadas finales
        self.line_id = None                                 # ID de la línea actual
        self.rect_id = None                                 # ID del rectángulo
        self.canvas_x_offset = 0                            # Desplazamiento x del canvas
        self.canvas_y_offset = 0                            # Desplazamiento y del canvas
        self.contour_canvas_ids = []                        # guardar los IDs de los contornos
        self.contour_original_coords = []                   # Guarda info original de 
        self.medicion_lineas = []                           # Coordenadas de las líneas medidas
        self.medicion_rectangulos = []                      # Coordenadas de los rectángulos medidos
        #                                                   #
        # --------------------------------------------------#
        # Variables para el conteo de objetos               #        
        self.manual_annotations = []                        # (x, y, r)
        self.evaluation_canvas_ids = []                     # Objetos visuales para TP, FP, FN
        self.match_threshold = 15                           # Distancia máxima para considerar coincidencia
        #                                                   #
        # --------------------------------------------------#
        # Variables para el estado de marcado               #
        #                                                   #
        # --------------------------------------------------#
        # Bandera para medir                                #
        self.is_measuring_reference = False                 # Bandera para medir la referencia
        self.is_measuring_rectangle = False                 # Bandera para medir la referencia
        #                                                   #
        # --------------------------------------------------#
        # Variables relacionadas con la medición de distancia#
        self.MedicionPixeles = 0.0                          # Medición en píxeles
        self.MedicionDistancia = 0.0                        # Medición en distancia
        self.MedicionLongitud = 0.0                         # Medición en longitud
        self.ValorPixel = tk.DoubleVar(value=1.0)           # Valor de píxeles
        self.ValorDistancia = tk.DoubleVar(value=1.0)       # Valor de distancia
        self.ValorLongitud = tk.DoubleVar(value=0.0)        # Valor de longitud
        self.ValorLargo = tk.DoubleVar(value=0.0)           # Valor del largo del rectángulo
        self.ValorAncho = tk.DoubleVar(value=0.0)           # Valor del ancho del rectángulo
        self.ValorConversion = 1.0                          # Valor de conversión
        self.conversion_text = tk.StringVar(value="0.0")    # Texto de conversión
        self.nuevo_limite_maximo = tk.DoubleVar(value=0.0)  # Nuevo límite máximo
        #                                                   #
        # --------------------------------------------------#
        # Valores iniciales paa la medición de contornos    #
        self.min_radius = 10.0                              # Radio mínimo para la detección de contornos
        self.max_radius = 50.0                              # Radio máximo para la detección de contornos
        self.min_dist = 20.0                                # Distancia mínima entre los centros de los círculos detectados     
        #                                                   #
        # --------------------------------------------------#
        # Unidad de medición                                #
        distance_units_var = tk.StringVar(value="unidad_inicial")  # Variable para las unidades de distancia
        #                                                   #
        # --------------------------------------------------#
        # Variables para seleccionar colores                #
        self.current_selection = 'lower'                    # Selección actual
        self.is_selecting_color = False                     # Bandera para selección de color
        self.current_selection = None                       # Selección actual de color
        self.lower_bound = None                             # Límite superior de la selección de color
        self.upper_bound = None                             # Límite superior de la selección de color
        self.temp_color = None                              # Para almacenar el color seleccionado temporalmente        
        #                                                   #
        # --------------------------------------------------#
        # Inicialización de variables globales              #
        self.Ancho_img = Ancho_img                          # Ancho de la imagen
        self.Alto_img = Alto_img                            # Alto de la imagen
        #                                                   #
        # --------------------------------------------------#
        # Variables para la cámara                          #        
        self.camera_active = False                          # Bandera para la cámara
        self.cap = None                                     # Cámara desactivada por defecto
        self.selected_camera_index = None                   # Índice de la cámara seleccionada
        #                                                   #
        #*************************************************************************************
        #*******        Configuración de la ventana principal       **************************
        #*************************************************************************************
        self.grid_rowconfigure(0, weight=1)                 # Fila superior: x1% de la altura
        self.grid_rowconfigure(1, weight=15)                # Fila inferior: x2% de la altura
        self.grid_columnconfigure(0, weight=1)              # Columna izquierda
        self.grid_columnconfigure(1, weight=12)             # Columna derecha
        #                                                   #
        #*************************************************************************************
        #*******            Configuración de los Frames             **************************
        #*************************************************************************************
        #                                                   #
        # Columna izquierda                                 #
        self.left_frame = tk.Frame(self, relief="flat", bd=1, bg=self.cget("bg"))
        self.left_frame.grid(row=0, column=0, sticky="nsew")#
        #                                                   #
        # Columna derecha                                   #
        self.right_frame = tk.Frame(self, relief="flat", bd=1, bg=self.cget("bg"))
        self.right_frame.grid(row=0, column=1, sticky="nsew")
        #                                                   #
        # Fila inferior que abarca ambas columnas           #
        self.bottom_frame = tk.Frame(self, relief="flat", bd=1, bg=self.cget("bg"))
        self.bottom_frame.grid(row=1, column=0, columnspan=2, sticky="nsew")
        #                                                   #
        # Configurar contenido de los frames                #
        self.setup_left_frame()                             # Configurar la columna izquierda
        self.setup_right_frame()                            # Configurar la columna derecha
        self.setup_bottom_frame()                           # Configurar la fila inferior
        #                                                   #
    #####################################################################################################
    #####################################################################################################
    #                              Imagen de la columna izquierda                                       #
    #####################################################################################################
    def setup_left_frame(self):                                                             #
        # Frame principal                                                                   #
        self.main_frame = tk.Frame(self.left_frame, bg=self.cget("bg"))                     #
        self.main_frame.grid(row=0, column=0, padx=5, pady=0, sticky="nsew")                #
        #                                                                                   #
        #                                                                                   #
        #***********************************************************************************#
        #              Visualización de imagen                                              #       
        #***********************************************************************************#
        # Nuevo Frame para los botones debajo del Notebook                                  #
        self.button_frame_below_canvas = tk.Frame(self.main_frame)                          #
        self.button_frame_below_canvas.grid(row=1, column=0, pady=0, sticky="ew")           #
        #***********************************************************************************#
        #                                                                                   #
        #                                                                                   #
        # Frame principal                                                                   #
        self.main_frame = tk.Frame(self)                                                    #
        self.main_frame.grid(row=0, column=0, padx=10, pady=0, sticky="nsew")               #
        #                                                                                   #
        # Dimensiones del canvas para la imagen #                                           #
        self.canvas_width = Ancho_img            # Ancho del canvas   Ancho_img = 600       #
        self.canvas_height = Alto_img            # Alto del canvas    Alto_img = 420        #
        #                                                                                   #
        # Frame para contener el Notebook y las barras de desplazamiento                    #
        self.notebook_frame = tk.Frame(self.main_frame)                                     #
        self.notebook_frame.grid(row=0, column=0, padx=10, pady=0, sticky="nsew")           #
        #                                                                                   #
        # Configuración de filas y columnas                                                 #
        self.notebook_frame.grid_rowconfigure(0, weight=1)                                  #
        self.notebook_frame.grid_columnconfigure(0, weight=1)                               #
        #                                                                                   #
        # Notebook                                                                          #                                                                         #
        self.notebook = ttk.Notebook(self.notebook_frame)                                   #
        self.notebook.grid(row=0, column=0, padx=10, pady=10, sticky="nsew")                #
        #                                                                                   #
        #                                                                                   #
        #***********************************************************************************#
        #*****************      Pestaña para la imagen temporal     ************************#
        #***********************************************************************************#
        #                                                                                   #
        # Pestaña para imagen temporal                                                      #
        self.canvas_tab = tk.Frame(self.notebook)                                           # Frame para la pestaña
        self.notebook.add(self.canvas_tab, text="Imagen temporal")                          # Título de la pestaña
        #                                                                                   #
        # Canvas para "Imagen Temporal" con barras de desplazamiento                        #
        self.canvas = tk.Canvas(self.canvas_tab, bg="gray", width=self.canvas_width, height=self.canvas_height)
        self.canvas.grid(row=0, column=0, sticky="nsew")                                    #
        #                                                                                   #
        # Barras de desplazamiento para el canvas                                           #
        self.v_scrollbar = tk.Scrollbar(self.canvas_tab, orient=tk.VERTICAL, command=self.canvas.yview)
        self.v_scrollbar.grid(row=0, column=1, sticky="ns")                                 #
        self.h_scrollbar = tk.Scrollbar(self.canvas_tab, orient=tk.HORIZONTAL, command=self.canvas.xview)
        self.h_scrollbar.grid(row=1, column=0, sticky="ew")                                 #
        self.canvas.config(yscrollcommand=self.v_scrollbar.set, xscrollcommand=self.h_scrollbar.set)
        #                                                                                   #
        # Variables para mostrar el color                                                   #
        self.canvas.bind("<Button-1>", self.handle_color_selection)                         #
        #                                                                                   #        
        #***********************************************************************************#
        #*****************      Pestaña para imagen original          **********************#
        #***********************************************************************************# 
        #                                                                                   #
        # Pestaña para las imagen original                                                  #
        self.canvas_tab_temp = tk.Frame(self.notebook, relief="flat")                       # Frame para la pestaña
        self.notebook.add(self.canvas_tab_temp, text="Imagen original")                     # Título de la pestaña
        #                                                                                   #
        # Canvas para "Imagen Original" con barras de desplazamiento                        #
        self.canvas_temp = tk.Canvas(self.canvas_tab_temp, bg="gray", width=self.canvas_width, height=self.canvas_height)
        self.canvas_temp.grid(row=0, column=0, sticky="nsew")                               #
        #                                                                                   #
        # Barras de desplazamiento para el canvas                                           #
        self.v_scrollbar_temp = tk.Scrollbar(self.canvas_tab_temp, orient=tk.VERTICAL, command=self.canvas_temp.yview)
        self.v_scrollbar_temp.grid(row=0, column=1, sticky="ns")                            #
        self.h_scrollbar_temp = tk.Scrollbar(self.canvas_tab_temp, orient=tk.HORIZONTAL, command=self.canvas_temp.xview)
        self.h_scrollbar_temp.grid(row=1, column=0, sticky="ew")                            #
        self.canvas_temp.config(yscrollcommand=self.v_scrollbar_temp.set, xscrollcommand=self.h_scrollbar_temp.set)
        #                                                                                   #
        #                                                                                   #
        #***********************************************************************************#
        #********************          Pestaña para resultados          ********************#
        #***********************************************************************************#
        #                                                                                   #
        # Configuración de la pestaña "Resultados"                                          #
        self.canvas_tab_results = tk.Frame(self.notebook, relief="flat")                    #     
        self.notebook.add(self.canvas_tab_results, text="Resultados")                       # Título de la pestaña
        #                                                                                   #
        # Canvas principal para desplazamiento                                              #
        self.results_canvas = tk.Canvas(self.canvas_tab_results, bg=self.cget("bg"))        #
        self.results_canvas.grid(row=0, column=0, sticky="nsew")                            #
        #                                                                                   #
        # Frame contenedor dentro del Canvas                                                #
        self.results_frame = tk.Frame(self.results_canvas, bg=self.cget("bg"))              #
        self.results_canvas.create_window((0, 0), window=self.results_frame, anchor="nw")   #
        #                                                                                   #
        # Configuración de grid para la pestaña "Resultados"                                #
        self.canvas_tab_results.grid_rowconfigure(0, weight=1)                              #
        self.canvas_tab_results.grid_columnconfigure(0, weight=1)                           #
        #                                                                                   #
        # Configuración del layout de la pestaña                                            #
        self.results_frame.grid_columnconfigure(0, weight=0, minsize=150)                   # Columna izquierda (tabla)
        self.results_frame.grid_columnconfigure(1, weight=0, minsize=250)                   # Columna derecha (histograma y estadísticas)
        self.results_frame.grid_rowconfigure(0, weight=0, minsize=300)                      # Altura compartida entre las dos columnas
        #                                                                                   #
        # Frame para la tabla (Columna izquierda)                                           #
        self.table_frame = tk.Frame(self.results_frame, bg=self.cget("bg"))                 #
        self.table_frame.grid(row=0, column=0, sticky="nsew", padx=5, pady=5)               #
        #                                                                                   #
        # Configuración de la tabla                                                         #
        self.results_table = ttk.Treeview(                                                  #
            self.table_frame,                                                               #
            columns=("Medicion", "Diámetro"),                                               #
            show="headings",                                                                #
            height=18,                                                                      #
        )                                                                                   #
        self.results_table.grid(row=0, column=0, sticky="nsew")                             #
        self.results_table.heading("Medicion", text="Medición")                             #
        self.results_table.heading("Diámetro", text="Diámetro")                             #
        self.results_table.column("Medicion", width=80, anchor="center")                    #
        self.results_table.column("Diámetro", width=80, anchor="center")                    #
        #                                                                                   #
        # Barras de desplazamiento para la tabla                                            #
        self.v_scrollbar_table = tk.Scrollbar(self.table_frame, orient=tk.VERTICAL, command=self.results_table.yview)
        self.v_scrollbar_table.grid(row=0, column=1, sticky="ns")                           #
        self.results_table.config(yscrollcommand=self.v_scrollbar_table.set)                #
        #                                                                                   #
        #-------------------------------------------------------------------#----------------------------------#
        #-------------------  Funciones para la tabla   --------------------#
        #-------------------------------------------------------------------#----------------------------------#
        # Función para limpiar la tabla                                     #
        def clear_table():                                                  # Función para limpiar la tabla
            for item in self.results_table.get_children():                  #
                self.results_table.delete(item)                             #
            for widget in self.hist_canvas.winfo_children():                # Limpiar el canvas del histograma
                widget.destroy()                                            # 
            for widget in self.stats_frame.winfo_children():                # Limpiar las estadísticas mostradas
                widget.destroy()                                            #
        #                                                                   #                                   #
        # Función para exportar los datos de la tabla ----------------------#-----------------------------------#
        def export_data():                                                  # Función para exportar los datos
            file_path = tk.filedialog.asksaveasfilename(defaultextension=".dat", filetypes=[("Archivos .dat", "*.dat")])
            if not file_path:                                               # Si no se selecciona un archivo
                return                                                      #
            with open(file_path, "w") as file:                              # Abrir el archivo en modo escritura
                file.write("Medicion\tDiámetro\n")                          # Encabezados de las columnas
                for row in self.results_table.get_children():               # Agregar filas
                    row_values = self.results_table.item(row, "values")     # Valores de la fila    
                    file.write("\t".join(row_values) + "\n")                # Escribir los valores en el archivo
            tk.messagebox.showinfo("Exportación exitosa", "Los datos se han exportado correctamente.") # Mensaje de éxito
        #                                                                   #
        # Función para eliminar una fila seleccionada ----------------------#-----------------------------------#        
        def delete_row():                                                   #
            selected_item = self.results_table.selection()                  # Fila seleccionada
            if selected_item:                                               #
                self.results_table.delete(selected_item)                    # Eliminar la fila seleccionada
        #                                                                   #
                # Algoritmo para actualizar los números de medición         #
                for idx, item in enumerate(self.results_table.get_children(), start=1):
                    # Actualizar el número de medición (columna "Medición") #
                    current_values = self.results_table.item(item, "values")#
                    self.results_table.item(item, values=(idx, current_values[1]))  # Actualizar solo la columna "Medición"
            else:                                                           #
                messagebox.showwarning("Advertencia", "Seleccione una fila para eliminar.")  # Mensaje de advertencia  
        #                                                                   #
        # Función para crear el menú contextual y destruirlo si es necesario#-----------------------------------#
        def show_context_menu(event):                                       # Función para mostrar el menú contextual
            if hasattr(self, "context_menu") and self.context_menu:         # Verificar si existe un menú contextual
                self.context_menu.destroy()                                 #    
            self.context_menu = tk.Menu(self.results_table, tearoff=0)      #
            self.context_menu.add_command(label="Eliminar fila", command=delete_row) # Agregar opción para eliminar fila
            self.context_menu.post(event.x_root, event.y_root)              # Mostrar el menú en la posición del cursor
            self.results_table.bind("<Button-1>", hide_context_menu)        # Ocultar el menú con clic izquierdo    
        #                                                                   # 
        # Función para ocultar el menú contextual   ------------------------#----------------------------------#
        def hide_context_menu(event=None):                                  #
            if hasattr(self, "context_menu") and self.context_menu:         #
                self.context_menu.destroy()                                 #
                self.context_menu = None                                    #
            self.results_table.unbind("<Button-1>")                         # Desvincular el evento de clic izquierdo
        #                                                                   #
        # Vincular el menú contextual y la eliminación con tecla de "Suprimir"
        self.results_table.bind("<Button-3>", show_context_menu)            # Mostrar menú contextual con clic derecho
        self.results_table.bind("<Delete>", lambda event: delete_row())     # Eliminar fila con la tecla "Suprimir"
        #                                                                   #        
        #-------------------------------------------------------------------#----------------------------------#
        #                                                                   #        
        # Frame derecho (Columna derecha)                                   #
        self.right_frame = tk.Frame(self.results_frame, bg=self.cget("bg")) #
        self.right_frame.grid(row=0, column=1, sticky="nsew", padx=5, pady=2)
        #                                                                   #
        # Configuración del layout dentro de la columna derecha             #
        self.right_frame.grid_rowconfigure(0, weight=1, minsize=100)        # Parte superior (Histograma)
        self.right_frame.grid_rowconfigure(1, weight=1, minsize=100)        # Parte inferior (Estadísticas)
        #                                                                   #
        # Histograma (Parte superior)                                       #
        self.right_top_frame = tk.Frame(self.right_frame, bg="white", relief="groove", borderwidth=1)
        self.right_top_frame.grid(row=0, column=0, sticky="nsew", padx=5, pady=2)
        #                                                                   #
        self.hist_canvas = tk.Canvas(self.right_top_frame, bg="white")      #
        self.hist_canvas.pack(fill="both", expand=True)                     #
        #                                                                   #
        # Estadísticas (Parte inferior)                                     #
        self.right_bottom_frame = tk.Frame(self.right_frame, bg="white", relief="groove", borderwidth=1)
        self.right_bottom_frame.grid(row=1, column=0, sticky="nsew", padx=5, pady=2)
        #                                                                   #
        self.stats_frame = tk.Frame(self.right_bottom_frame, bg="white")    #
        self.stats_frame.pack(fill="both", expand=True, padx=5, pady=5)     #
        #                                                                   #
        # Configuración de Canvas para ajustarse al contenido               #
        def configure_canvas(event):                                        #
            self.results_canvas.configure(scrollregion=self.results_canvas.bbox("all"))
        #                                                                   #
        self.results_frame.bind("<Configure>", configure_canvas)            #
        #                                                                   #
        #                                                                   #
        #************************************************************************************#
        #********************          Pestaña para la cámara           *********************#
        #************************************************************************************#
        #                                                                                    #
        # Crear una nueva pestaña para la cámara                                             #   
        self.camera_tab = tk.Frame(self.notebook, relief="flat")                             #
        self.notebook.add(self.camera_tab, text="Cámara")                                    #
        #                                                                                    #
        # Canvas en la pestaña de la cámara para mostrar el feed                             #
        self.camera_canvas = tk.Canvas(self.camera_tab, bg="gray", width=self.canvas_width, height=self.canvas_height)
        self.camera_canvas.grid(row=0, column=0, sticky="nsew")                              #
        #                                                                                    #
        #                                                                                    #
        #************************************************************************************#
        #              Botones bajo la imagen                                                #       
        #************************************************************************************#
        # Nuevo Frame para los botones debajo del Notebook                                   #
        self.button_frame_below_canvas = tk.Frame(self.main_frame)                           #
        self.button_frame_below_canvas.grid(row=1, column=0, pady=0, sticky="ew")            #
        #************************************************************************************#
        #
        # Botón "Directorio" para cargar imágenes
        btn_load_images = tk.Button(self.button_frame_below_canvas, text="Directorio", command=self.load_images)
        btn_load_images.pack(side=tk.LEFT, padx=5, pady=0)
        #
        # Botón "Actualizar" para refrescar las imágenes
        btn_refresh_images = tk.Button(self.button_frame_below_canvas, text="Actualizar", command=self.refresh_images)
        btn_refresh_images.pack(side=tk.LEFT, padx=0, pady=0)
        #
        # Botón "Guardar" para guardar la imagen procesada
        btn_save = tk.Button(self.button_frame_below_canvas, text="Guardar imagen", command=self.save_image)
        btn_save.pack(side=tk.LEFT, padx=0, pady=0)
        #
        # Botón para limpiar la tabla
        btn_clear_table = tk.Button(self.button_frame_below_canvas, text="Limpiar tabla", command=clear_table)
        btn_clear_table.pack(side=tk.LEFT, padx=0, pady=0)
        #
        # Botón para exportar los datos de la tabla
        btn_export_data = tk.Button(self.button_frame_below_canvas, text="Exportar datos", command=export_data)
        btn_export_data.pack(side=tk.LEFT, padx=0, pady=0)
        #
        # Botón para calcular estadísticas
        self.calculate_stats_button = tk.Button(self.button_frame_below_canvas, text="Gráfica", command=lambda: self.calculate_statistics(self.get_table_values()))
        self.calculate_stats_button.pack(side="left", padx=0, pady=0)
        #
        #     
    #####################################################################################################
    #####################################################################################################
    #                              Botones de la columna derecha                                        #
    #####################################################################################################
    #                                                                   #                               #
    # Configurar el frame de la columna derecha                         #                               #
    def setup_right_frame(self):                                        #                               #
        # Frame superior                                                #                               #
        frame_top = tk.Frame(self.right_frame, bg=self.cget("bg"))      #                               #
        frame_top.grid(row=0, column=0, padx=5, pady=5, sticky="w")     #                               #
        self.right_frame.grid_rowconfigure(0, weight=0)                 # Primera fila sea dinámica     #
        self.right_frame.grid_columnconfigure(0, weight=1)              # Primera columna sea dinámica  #
        #                                                               #                               #
        #                                                               #                               #
        #+++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++#
        #+++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++#
        #                       Columna Derecha: Fila 1                                 #
        #+++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++#
        #+++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++#        
        # Frame para los botones a la derecha de la imagen                      #
        self.button_frame = tk.Frame(self.main_frame)                           # Frame para los botones
        self.button_frame.grid(row=0, column=2, sticky="n")                     # Alinea todo el marco superior
        #                                                                       #
        # Subframes para los botones                                            #
        self.button_frame_top = tk.Frame(self.button_frame)                     # 
        self.button_frame_top.pack(side=tk.TOP, padx=2, pady=0, anchor="n")     # Márgenes reducidos y alineación superior
        #                                                                       #
        self.button_frame_middle = tk.Frame(self.button_frame)                  # 
        self.button_frame_middle.pack(side=tk.TOP, padx=2, pady=2, anchor="n")  # Márgenes reducidos y alineación superior
        #                                                                       #
        self.button_frame_bottom = tk.Frame(self.button_frame)                  # 
        self.button_frame_bottom.pack(side=tk.TOP, padx=2, pady=2, anchor="n")  # Márgenes reducidos y alineación superior
        #                                                                       #
        #                                                                       #
	    ###################################################################################
        ##################               Fila 1 de botones        #########################
	    ###################################################################################
        #        
        # Frame para la fila 1
        self.button_row_1 = tk.Frame(self.button_frame_bottom)
        self.button_row_1.pack(side=tk.TOP, anchor="w", pady=0)  # Reduce el margen vertical

        # Botón zoom para ampliar la imagen
        zoom_in_button = tk.Button(self.button_row_1, text="Zoom +", command=self.zoom_in)
        zoom_in_button.pack(side=tk.LEFT, padx=4, pady=2)

        # Botón zoom para reducir la imagen
        zoom_out_button = tk.Button(self.button_row_1, text="Zoom -", command=self.zoom_out)
        zoom_out_button.pack(side=tk.LEFT, padx=4, pady=2)

        # Botón para deshacer cambios
        btn_undo = tk.Button(self.button_row_1, text="Deshacer", command=self.undo_change)
        btn_undo.pack(side=tk.LEFT, padx=4, pady=2)

        # Botón para rehacer cambios
        btn_redo = tk.Button(self.button_row_1, text="Rehacer", command=self.redo_change)
        btn_redo.pack(side=tk.LEFT, padx=4, pady=2)

        # Botón desplegable para seleccionar/activar/desactivar cámara
        self.toggle_button = tk.Menubutton(self.button_row_1, text="Cámara", relief="raised", direction="below")
        self.toggle_button.pack(side=tk.LEFT, padx=4, pady=2)
        # Crear el menú asociado al botón desplegable
        self.menu = tk.Menu(self.toggle_button, tearoff=0)
        self.toggle_button.config(menu=self.menu)
        # Agregar la opción inicial para buscar cámaras
        self.menu.add_command(label="Buscar cámaras", command=self.search_cameras)

        # Botón para tomar una foto
        btn_take_photo = tk.Button(self.button_row_1, text="Tomar Foto", command=self.take_photo)
        btn_take_photo.pack(side=tk.LEFT, padx=4, pady=2)

        # Botón para ayuda
        btn_ayuda_usuario = tk.Button(self.button_row_1, text="Ayuda", command=self.ayuda_usuario)
        btn_ayuda_usuario.pack(side=tk.LEFT, padx=4, pady=2)
        #
        #
        #+++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++#
        #+++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++#
        #                       Parámetros de referencia                                #
        #                       Columna Derecha: Fila 2                                 #
        #+++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++#
        #+++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++#
        #
        # Frame para la fila 4
        self.button_row_4 = tk.Frame(self.button_frame_bottom)
        self.button_row_4.pack(side=tk.TOP, anchor="w")
        #
        ######################################### Frame para el recuadro con ancho y alto fijos #########################
        contour_frame = tk.LabelFrame(          # Frame para el recuadro
            self.button_row_4,                  # Frame contenedor
            text="Parámetros de referencia",    # Título del recuadro
            padx=0,                             # Espaciado interno
            pady=0,                             # Espaciado externo
            labelanchor="nw",                   # Alinear la etiqueta en la parte superior izquierda
            width=630,                          # Ancho fijo del recuadro
            height=110,                         # Alto fijo del recuadro
            font=("Arial", 10)                  # Establecer la fuente en negrita
        )                                       # Fin de la configuración del recuadro
        contour_frame.pack_propagate(False)     # Deshabilitar la redimensión del recuadro
        contour_frame.pack(side=tk.TOP, anchor="w", padx=5, pady=0)

        # Variable para rastrear la forma seleccionada
        self.selected_shape = tk.StringVar(value="")
        # Validación de entrada: Solo números               #
        vcmd = (self.register(self.validar_numero), '%P')   # Validar la entrada de números

        # Función para actualizar las etiquetas de unidades             #
        def update_labels(new_unit):                                    #
            self.lengthLine_unit_label.config(text=new_unit)            # Unidades para la línea
           # self.width_unit_label.config(text=new_unit)                 # unidades para el rectángulo
            self.unidadesConversion_label.config(text=f"{new_unit}/px") # Unidades de conversión

        # Nueva fila de botones (Referencia)
        reference_frame = tk.Frame(contour_frame)
        reference_frame.pack(side=tk.TOP, fill=tk.X, padx=0, pady=0)
        #--------------------------------------------------------------------------------#
        # Variables para almacenar los valores de pixeles y distancia
        self.pixels = 0                                 # Valor de píxeles inicial
        self.distance = 0                               # Valor de distancia inicial
        self.reference = 0                              # Valor de referencia inicial
        self.measure_reference = 0                      # Valor de medición de referencia
        #                                               #
        # Variables para almacenar valores              #
        self.ValorPixel = tk.DoubleVar(value=0.0)       # Valor de píxeles
        self.ValorDistancia = tk.DoubleVar(value=0.0)   # Valor de distancia
        self.ValorLongitud = tk.DoubleVar(value=0.0)    # Valor de longitud
        self.ValorLargo = tk.DoubleVar(value=0.0)       # Valor de largo
        self.ValorAncho = tk.DoubleVar(value=0.0)       # Valor de ancho
        #                                               #
        #---------------------------------------------------------------------------#
        # Guardar referencias de botones                #
        self.button_states = {                          #
              "measure_reference": False,               # Estado del botón "Medir referencia"
              "pixels": False,                          # Estado del botón "Pixeles"
              "distance": False,                        # Estado del botón "Distancia"
              "reference": False,                       # Estado del botón "Utilizar referencia"
              "lengthLine": False,                      # Estado del botón "Medir longitud"
              }                                         #
        #---------------------------------------------------------------------------#
        # Función para manejar la selección de los botones                          #
        def toggle_button(button_type):                                             #
            """Activa/desactiva los botones y cambia el color."""                   #   
            if button_type == "measure_reference":                                  #
                # Cambiar estado del botón "Medir referencia"                       #
                if self.button_states["measure_reference"]:                         # Si el botón está activo
                    measure_reference_button.config(relief=tk.RAISED, bg="lightgray") # Cambiar el estilo del botón
                    self.button_states["measure_reference"] = False                 # Cambiar el estado del botón
                    self.pixels_entry.config(state=tk.NORMAL)                       # Habilitar la entrada de pixeles
                    self.distance_entry.config(state=tk.NORMAL)                     # Habilitar la entrada de distancia
                    self.pixels_button.config(bg="lightgray", relief=tk.RAISED)     # Deseleccionar el botón "Pixeles"
                    self.distance_button.config(bg="lightgray", relief=tk.RAISED)   # Deseleccionar el botón "Distancia"
                    # Cambiar estado del botón "Medir longitud"                     #
                    self.use_lengthLine_button.config(relief=tk.RAISED, bg="lightgray")  # Cambiar el estilo del botón
                    self.button_states["lengthLine"] = False                        # Cambiar el estado del botón
                    # Desactivar los eventos de línea                               #
                    self.canvas.unbind("<ButtonPress-1>")                           # Desactivar eventos de línea
                    self.canvas.unbind("<B1-Motion>")                               # Desactivar eventos de línea
                    self.canvas.unbind("<ButtonRelease-1>")                         # Desactivar eventos de línea
                    # Desactivar la medición de referencia                          #
                    self.is_measuring_reference = False                             # Desactivar la medición de referencia
                else:                                                               # Si el botón está inactivo
                    measure_reference_button.config(relief=tk.SUNKEN, bg="lightgreen") # Cambiar el estilo del botón
                    self.button_states["measure_reference"] = True                  # Cambiar el estado del botón
                    self.pixels_button.config(relief=tk.RAISED, bg="lightgray", state=tk.NORMAL) # Deseleccionar el botón "Pixeles"
                    self.button_states["pixels"] = False                            # Inicializar el estado del boton "Pixeles"
                    self.pixels_entry.config(state=tk.NORMAL)                       # Habilitar el input de pixeles
                    self.distance_button.config(relief=tk.RAISED, bg="lightgray", state=tk.NORMAL) # Deseleccionar el botón "Distancia"
                    self.button_states["distance"] = False                          # Inicializar el estado del botón "Distancia"
                    self.distance_entry.config(state=tk.NORMAL)                     # Habilitar la entrada de distancia
                    use_reference_button.config(relief=tk.RAISED, bg="lightgray")   # Inicializar el estado del botón "Utilizar referencia"
                    self.button_states["reference"] = False                         # Inicializar el estado del botón "Utilizar referencia"
                    # Activar eventos de línea                                      #
                    self.canvas.bind("<ButtonPress-1>", self.start_line)            # Activar eventos de línea
                    self.canvas.bind("<B1-Motion>", self.draw_line)                 # Activar eventos de línea
                    self.canvas.bind("<ButtonRelease-1>", self.finish_line)         # Activar eventos de línea
                    self.is_measuring_reference = True                              # Activar la medición de referenciagulo
                    # Cambiar estado del botón "Medir longitud"                     #
                    self.use_lengthLine_button.config(relief=tk.RAISED, bg="lightgray")  # Cambiar el estilo del botón
                    self.button_states["lengthLine"] = False                        # Cambiar el estado del botón
                    self.lengthLine_entry.config(state=tk.DISABLED)                 # Deshabilitar la entrada de longitud
            elif button_type == "pixels":                                           #
                # Cambiar estado del botón "Pixeles"                                #
                if self.button_states["pixels"]:                                    # Si el botón está activo
                    self.pixels_button.config(relief=tk.RAISED, bg="lightgray")     # Cambiar el estilo del botón
                    self.button_states["pixels"] = False                            # Cambiar el estado del botón
                    self.pixels_entry.config(state=tk.NORMAL)                       # Habilitar la entrada de pixeles
                    # Cambiar estado del botón "Longitud"                           #
                    self.use_lengthLine_button.config(relief=tk.RAISED, bg="lightgray")  # Cambiar el estilo del botón
                    self.button_states["lengthLine"] = False                        # Cambiar el estado del botón
                    # Habilitar botón "Utilizar referencia"                         #
                    use_reference_button.config(relief=tk.RAISED, bg="lightgray")   # Cambiar el estilo del botón 
                    self.lengthLine_entry.config(state=tk.DISABLED)                 # Deshabilitar la entrada de longitud
                else:                                                               #                       
                    self.pixels_button.config(relief=tk.SUNKEN, bg="lightgreen")    # Cambiar el estilo del botón
                    self.button_states["pixels"] = True                             # Cambiar el estado del botón
                    self.pixels_entry.config(state=tk.DISABLED)                     # Deshabilitar la entrada de pixeles
                    # Cambiar estado del botón "Longitud"                           #
                    self.use_lengthLine_button.config(relief=tk.RAISED, bg="lightgray")  # Cambiar el estilo del botón
                    self.button_states["lengthLine"] = False                        # Cambiar el estado del botón
                    # Deshabilitar la entrada de longitud, lado L y A               #
                    self.lengthLine_entry.config(state=tk.DISABLED)                 # Deshabilitar la entrada de longitud
                    # Desactivar los eventos de línea                               #
                    self.canvas.unbind("<ButtonPress-1>")                           # Desactivar eventos de línea
                    self.canvas.unbind("<B1-Motion>")                               # Desactivar eventos de línea
                    self.canvas.unbind("<ButtonRelease-1>")                         # Desactivar eventos de línea
            elif button_type == "distance":                                         #    
                # Cambiar estado del botón "Distancia"                              #
                if self.button_states["distance"]:                                  # Si el botón está activo
                    self.distance_button.config(relief=tk.RAISED, bg="lightgray")   # Cambiar el estilo del botón
                    self.button_states["distance"] = False                          # Cambiar el estado del botón
                    self.distance_entry.config(state=tk.NORMAL)                     # Habilitar la entrada de distancia
                    # Cambiar estado del botón "Longitud"                           #
                    self.use_lengthLine_button.config(relief=tk.RAISED, bg="lightgray")  # Cambiar el estilo del botón
                    self.button_states["lengthLine"] = False                        # Cambiar el estado del botón
                    # Habilitar botón "Utilizar referencia"                         #
                    use_reference_button.config(relief=tk.RAISED, bg="lightgray")   # Cambiar el estilo del botón
                    self.button_states["reference"] = True                          # Cambiar el estado del botón
                    # Deshabilitar la entrada de longitud, lado L y A               #
                    self.lengthLine_entry.config(state=tk.DISABLED)                 # Deshabilitar la entrada de longitud
                else:                                                               # Si el botón está inactivo
                   self.distance_button.config(relief=tk.SUNKEN, bg="lightgreen")   # Cambiar el estilo del botón
                   self.button_states["distance"] = True                            # Cambiar el estado del botón
                   self.distance_entry.config(state=tk.DISABLED)                    # Deshabilitar la entrada de distancia
                   self.pixels_button.config(relief=tk.SUNKEN, bg="lightgreen")     # Cambiar el estilo del botón
                   self.button_states["pixels"] = True                              # Cambiar el estado del botón
                   self.pixels_entry.config(state=tk.DISABLED)                      # Deshabilitar la entrada de pixeles
                   # Deshabilitar la entrada de longitud, lado L y A                #
                   self.lengthLine_entry.config(state=tk.DISABLED)                  # Deshabilitar la entrada de longitud
                   # Desactivar los eventos de línea                                #
                   self.canvas.unbind("<ButtonPress-1>")                            # Desactivar eventos de línea
                   self.canvas.unbind("<B1-Motion>")                                # Desactivar eventos de línea
                   self.canvas.unbind("<ButtonRelease-1>")                          # Desactivar eventos de línea
            elif button_type == "reference":                                        # Cambiar estado del botón "Utilizar referencia"
                # Cambiar estado del botón "Utilizar referencia"                    #
                if self.button_states["reference"]:                                 # Si el botón está activo 
                    use_reference_button.config(relief=tk.RAISED, bg="lightgray")   # Cambiar el estilo del botón
                    self.button_states["reference"] = False                         # Cambiar el estado del botón
                    # Cambiar estado del botón "Medir longitud"                     #
                    self.use_lengthLine_button.config(relief=tk.RAISED, bg="lightgray")  # Cambiar el estilo del botón
                    self.button_states["lengthLine"] = False                        # Cambiar el estado del botón
                    # Deshabilitar la entrada de longitud, lado L y A               #
                    self.lengthLine_entry.config(state=tk.DISABLED)                 # Deshabilitar la entrada de longitud
                else:                                                               # Si el botón está inactivo                      
                    use_reference_button.config(relief=tk.SUNKEN, bg="lightcoral")  # Cambiar el estilo del botón
                    self.button_states["reference"] = True                          # Cambiar el estado del botón
                    measure_reference_button.config(relief=tk.RAISED, bg="lightgray")# Cambiar el estilo del botón
                    self.button_states["measure_reference"] = False                 # Cambiar el estado del botón
                    # Cambiar estado del botón "Pixeles" y "Distancia"              #
                    self.pixels_button.config(relief=tk.SUNKEN, bg="lightgreen")    # Cambiar el estilo del botón
                    self.button_states["pixels"] = False                            # Cambiar el estado del botón
                    self.pixels_entry.config(state=tk.DISABLED)                     # Deshabilitar la entrada de pixeles
                    self.distance_button.config(relief=tk.SUNKEN, bg="lightgreen")  # Cambiar el estilo del botón
                    self.distance_entry.config(state=tk.DISABLED)                   # Deshabilitar la entrada de distancia
                    # Desactivar los eventos de línea del measure_reference         #
                    self.canvas.unbind("<ButtonPress-1>")                           # Desactivar eventos de línea
                    self.canvas.unbind("<B1-Motion>")                               # Desactivar eventos de línea
                    self.canvas.unbind("<ButtonRelease-1>")                         # Desactivar eventos de línea
                    self.is_measuring_reference = False                             # Desactivar la medición de referencia
                    # Deshabilitar la entrada de longitud, lado L y A               #
                    self.lengthLine_entry.config(state=tk.DISABLED)                 # Habilitar la entrada de longitud
            elif button_type == "lengthLine":                                       # Cambiar estado del botón "Utilizar referencia"
                # Cambiar estado del botón "Utilizar referencia"                    #
                if self.button_states["lengthLine"]:                                # Si el botón está activo 
                    use_reference_button.config(relief=tk.SUNKEN, bg="lightcoral")  # Cambiar el estilo del botón
                    self.button_states["reference"] = True                          # Cambiar el estado del botón
                    # Cambiar estado del botón "Longitud"                           #
                    self.use_lengthLine_button.config(relief=tk.RAISED, bg="lightgray")  # Cambiar el estilo del botón
                    self.button_states["lengthLine"] = False                        # Cambiar el estado del botón
                    self.lengthLine_entry.config(state=tk.DISABLED)                 # Habilitar la entrada de longitud
                    # Cambiar de color los botones de pixeles y distancia           #
                    self.pixels_button.config(relief=tk.SUNKEN, bg="lightgreen")    # Cambiar el estilo del botón
                    self.pixels_entry.config(state=tk.DISABLED)                     # Deshabilitar la entrada de pixeles
                    self.distance_button.config(relief=tk.SUNKEN, bg="lightgreen")  # Cambiar el estilo del botón
                    self.distance_entry.config(state=tk.DISABLED)                   # Deshabilitar la entrada de distancia
                    # Deshabilitar la entrada de longitud, lado L y A               #
                    self.lengthLine_entry.config(state=tk.DISABLED)                 # Deshabilitar la entrada de longitud
                    # Desactivar los eventos de línea del measure_reference         #
                    self.canvas.unbind("<ButtonPress-1>")                           # Desactivar eventos de línea
                    self.canvas.unbind("<B1-Motion>")                               # Desactivar eventos de línea
                    self.canvas.unbind("<ButtonRelease-1>")                         # Desactivar eventos de línea
                    self.is_measuring_reference = False                             # Desactivar la medición de referencia
                else:                                                               # Si el botón está inactivo
                    use_reference_button.config(relief=tk.SUNKEN, bg="lightcoral")  # Cambiar el estilo del botón
                    self.button_states["reference"] = True                          # Cambiar el estado del botón
                    measure_reference_button.config(relief=tk.RAISED, bg="lightgray")# Cambiar el estilo del botón
                    self.button_states["measure_reference"] = False                 # Cambiar el estado del botón
                    # Cambiar de color los botones de pixeles y distancia           #
                    self.pixels_button.config(relief=tk.SUNKEN, bg="lightgray")     # Cambiar el estilo del botón
                    self.button_states["pixels"] = False                            # Cambiar el estado del botón
                    self.pixels_entry.config(state=tk.DISABLED)                     # Deshabilitar la entrada de pixeles
                    self.distance_button.config(relief=tk.SUNKEN, bg="lightgray")   # Cambiar el estilo del botón
                    self.button_states["distance"] = False                          # Cambiar el estado del botón
                    self.distance_entry.config(state=tk.DISABLED)                   # Deshabilitar la entrada de distancia
                    # Cambiar estado del botón "Longitud"                           #
                    self.use_lengthLine_button.config(relief=tk.SUNKEN, bg="lightgreen") # Cambiar el estilo del botón
                    self.button_states["lengthLine"] = True                         # Cambiar el estado del botón
                    self.lengthLine_entry.config(state=tk.NORMAL)                   # Habilitar la entrada de longitud
                    # Activar eventos de línea                                      #
                    self.canvas.bind("<ButtonPress-1>", self.start_line)            # Activar eventos de línea
                    self.canvas.bind("<B1-Motion>", self.draw_line)                 # Activar eventos de línea
                    self.canvas.bind("<ButtonRelease-1>", self.finish_line)         # Activar eventos de línea
                    self.is_measuring_reference = True                              # Activar la medición de referencia
        #---------------------------------------------------------------------------#--------------------------------#

        # Función para medir la referencia (habilitar dibujo)               #
        def measure_reference():                                            # Accion al presionar el botón medir referencia
            toggle_button("measure_reference")                              # Llamar a la función para activar/desactivar el botón
        measure_reference_button = tk.Button(reference_frame,               # Botón para medir la referencia
                                     text="Medir\nreferencia",              # Texto del botón con salto de línea
                                     command=lambda: toggle_button("measure_reference"),  # Comando al presionar el botón
                                     relief=tk.RAISED,                      # Estilo del borde
                                     activebackground="lightgray",          # Color de fondo activo
                                     activeforeground="black",              # Color de texto activo
                                     )                                      # Fin de la configuración del botón
        measure_reference_button.pack(side=tk.LEFT, padx=5)                 # Alinear a la izquierda y agregar margen


        # Botón "Pixeles"
        def use_pixels():                                       # Acción al presionar el botón "Pixeles"
            print("Pixeles utilizados.")                        #
            toggle_button("pixels")

        self.pixels_button = tk.Button(
            reference_frame,
            text="Pixeles",
            bg="lightgray",
            command=lambda: toggle_button("pixels"),
            relief=tk.RAISED,
            activebackground="lightgray",
            activeforeground="black"
        )
        self.pixels_button.pack(side=tk.LEFT, padx=5)
        self.pixels_entry = tk.Entry(reference_frame, width=7, textvariable=self.ValorPixel, validate="key", validatecommand=vcmd)
        self.pixels_entry.pack(side=tk.LEFT, padx=0)            # Alinear a la izquierda y agregar margen
        # Obtener el valor como texto y convertirlo a float     #
        self.pixels_entry.delete(0, tk.END)                     # Borrar el contenido de la entrada
        self.pixels_entry.insert(0, "0.0")                      # Valor por defecto     
        # Conectar el evento de cambio de valor a la entrada de pixeles
        self.pixels_entry.bind("<FocusOut>", self.validar_y_actualizar)
        # Validar también al presionar Enter
        self.pixels_entry.bind("<Return>", lambda event: (
            self.validar_y_actualizar(),
            self.realizar_calculo(),
            self.toggle_estado_boton("pixels")
        ))

        # Símbolo "=" entre Pixeles y Distancia conocida
        equal_button = tk.Label(reference_frame, text="=", anchor="w")
        equal_button.pack(side=tk.LEFT, padx=0)

        # Botón "Distancia conocida"
        def use_lengthLine():                                   # Acción al presionar el botón "Longitud"
            print("Longitud utilizada.")                        #
            toggle_button("length")                             #
        # Botón "Distancia"                                     ###############################
        self.distance_button = tk.Button(
            reference_frame,
            text="Referencia",
            bg="lightgray",
            command=lambda: toggle_button("distance"),
            relief=tk.RAISED,
            activebackground="lightgray",
            activeforeground="black"
        )
        self.distance_button.pack(side=tk.LEFT, padx=5)
        # Entrada para la longitud conocida                     #
        self.distance_entry = tk.Entry(reference_frame, width=7, textvariable=self.ValorDistancia, validate="key", validatecommand=vcmd)
        self.distance_entry.pack(side=tk.LEFT, padx=10)         #
        # Obtener el valor como texto y convertirlo a float     #
        self.distance_entry.delete(0, tk.END)                   # Borrar el contenido de la entrada
        self.distance_entry.insert(0, "0.0")                    # Valor por defecto
        # Conectar el evento de cambio de valor a la entrada de distancia
        self.distance_entry.bind("<FocusOut>", self.validar_y_actualizar)
        # Validar también al presionar Enter
        self.distance_entry.bind("<Return>", lambda event: (
            self.validar_y_actualizar(),
            self.realizar_calculo(),
            self.toggle_estado_boton("distance")
        ))


        #***********************************************************#
        # Menú desplegable para unidades                            #
        self.distance_units_var = tk.StringVar(value="px")          #
        self.distance_units_menu = tk.OptionMenu(reference_frame,   #
                                          self.distance_units_var,  #
                   "px", "nm", "\u03bcm", "mm", "cm", "m",          #
                                            command=update_labels   #
                                            )                       #    
        self.distance_units_menu.config(width=3)                    # Establecer un ancho fijo de 10 caracteres
        self.distance_units_menu.pack(side=tk.LEFT, padx=5)         #
        #***********************************************************#
        radio_text = f"({self.distance_units_var.get()})"           # Texto para las unidades de distancia
        
        # Botón "Utilizar referencia" actualizado
        def use_reference():                                            # Acción al presionar el botón "Utilizar referencia"
            toggle_button("reference")                                  # Llamar a la función para activar/desactivar el botón
            self.realizar_calculo()                                     # Llama al método para realizar el cálculo
        use_reference_button = tk.Button(reference_frame,               # Botón "Utilizar referencia"
                                         text="Aplicar",                # Texto del botón
                                         command=use_reference,         # Comando al presionar el botón
                                         relief=tk.RAISED,              # Estilo del borde
                                         activebackground="lightgray",  # Color de fondo activo
                                         activeforeground="black",      # Color de texto activo
                                        )                               # Fin de la configuración del botón
        use_reference_button.pack(side=tk.LEFT, padx=10)                # Alinear a la izquierda y agregar margen

        # Botón y entrada para las mediciones de longitud en funcion del parámetro de referencia
        self.lengthLine_frame = tk.Frame(contour_frame)
        self.lengthLine_frame.pack(side=tk.LEFT, padx=5, pady=0)

        # Botón "Longitud"
        def use_lengthLine():                                           # Acción al presionar el botón "Longitud"
            toggle_button("lengthLine")                                 # Llamar a la función para activar/desactivar el botón
        self.use_lengthLine_button = tk.Button(
            self.lengthLine_frame,
            text="Longitud",
            command=lambda: toggle_button("lengthLine"),
            relief=tk.RAISED,
            activebackground="lightgray",
            activeforeground="black"
        )
        self.use_lengthLine_button.pack(side=tk.LEFT, padx=5)
        # Entrada para la longitud conocida
        self.lengthLine_entry = tk.Entry(self.lengthLine_frame, width=7, textvariable=self.ValorLongitud, validate="key", validatecommand=vcmd)
        self.lengthLine_entry.pack(side=tk.LEFT, padx=0)
        # Obtener el valor como texto y convertirlo a float
        self.lengthLine_entry.delete(0, tk.END)
        self.lengthLine_entry.insert(0, "0.0")  # Valor por defecto
        # Conectar el evento de cambio de valor a la entrada de distancia
        self.lengthLine_entry.bind("<FocusOut>", self.validar_y_actualizar)
        # Validar también al presionar Enter
        self.lengthLine_entry.bind("<Return>", self.validar_y_calcular)


        # Etiqueta para la unidad del Longitud
        self.lengthLine_unit_label = tk.Label(self.lengthLine_frame, text=self.distance_units_var.get(), anchor="w", width=3)
        self.lengthLine_unit_label.pack(side=tk.LEFT, padx=3)
        #
#        # Botón toggle para agregar mediciones a la tabla automáticamente
#        self.agregar_a_tabla = False  # Estado inicial
#        # Crear el botón
#        agregar_button = tk.Button(
#            self.lengthLine_frame,
#            text="Agregar a la tabla",  # Texto inicial
#            relief=tk.RAISED,
#            width=12
#        )
#        # Guardar el color de fondo por defecto del botón (funciona en todos los sistemas)
#        default_bg = agregar_button.cget("background")
#        agregar_button.pack(side=tk.LEFT, padx=5)
##        self.agregar_tooltip(self.lengthLine_frame, "Presiona para agregar los valores\nde la medición de la 'Longitud'")
#        # Función para alternar el estado del botón
#        def toggle_agregar_a_tabla():
#            self.agregar_a_tabla = not self.agregar_a_tabla
#            if self.agregar_a_tabla:
#                agregar_button.config(relief=tk.SUNKEN, bg="lightblue", text="Guardando")
#                self.agregar_tooltip(self.lengthLine_frame, "Presiona para agregar los valores\n'Longitud'")
#            else:
#                agregar_button.config(relief=tk.RAISED, bg=default_bg, text="Agregar a la tabla")
#                self.agregar_tooltip(self.lengthLine_frame, "Presiona para agregar\n'Longitud'")
#
#        # Asignar la función como comando del botón (después de definirla)
#        agregar_button.config(command=toggle_agregar_a_tabla)
#
#
        # Botón toggle para agregar mediciones a la tabla automáticamente
        self.agregar_a_tabla = False  # Estado inicial
        # Crear el botón
        agregar_button = tk.Button(
            self.lengthLine_frame,
            text="Agregar a la tabla",
            relief=tk.RAISED,
            width=15
        )
        # Guardar color de fondo por defecto
        default_bg = agregar_button.cget("background")
        agregar_button.pack(side=tk.LEFT, padx=5)
        # Función para actualizar tooltip (externo al toggle)
        def actualizar_tooltip_agregar():
            if self.agregar_a_tabla:
                self.agregar_tooltip(agregar_button, "Modo activo:\nSe agregará automáticamente\na la tabla la medición de 'Longitud'")
            else:
                self.agregar_tooltip(agregar_button, "Presiona para agregar la medición de\n'Longitud' a la tabla")
        # Función para alternar el estado del botón
        def toggle_agregar_a_tabla():
            self.agregar_a_tabla = not self.agregar_a_tabla
            if self.agregar_a_tabla:
                agregar_button.config(relief=tk.SUNKEN, bg="lightblue", text="Guardando")
            else:
                agregar_button.config(relief=tk.RAISED, bg=default_bg, text="Agregar a la tabla")
            actualizar_tooltip_agregar()
        # Asignar comando
        agregar_button.config(command=toggle_agregar_a_tabla)
        # Inicializar tooltip
        actualizar_tooltip_agregar()

        # Insertar espacio horizontal
        tk.Label(contour_frame, text="  ").pack(side=tk.LEFT, padx=10)
        
        # Frame para el rectángulo (Largo y Ancho)
        self.rectangle_frame = tk.Frame(contour_frame)
        self.rectangle_frame.pack(side=tk.LEFT, padx=5, pady=0)

        # Botón para resetear las variables de medición
        self.reset_button = tk.Button(self.rectangle_frame, text="Reiniciar valores", command=self.reset_measurement, width=11)
        self.reset_button.pack(side=tk.LEFT, padx=5, pady=1)

        #
        # Marco para el contorno
        self.conversion_frame = tk.Frame(self.rectangle_frame, relief=tk.GROOVE, bd=2, padx=5, pady=5)
        self.conversion_frame.pack(side=tk.LEFT, padx=5, pady=0)
        #
        # Etiqueta para mostrar el valor de conversión
        self.conversion_label = tk.Label(self.conversion_frame, text="0.0", anchor="w")
        self.conversion_label.pack(side=tk.LEFT, padx=5)
        #
        # Etiqueta para la unidad del rectángulo
        self.unidadesConversion_label = tk.Label(self.conversion_frame, text=self.distance_units_var.get() + "/px", anchor="w", width=6)
        self.unidadesConversion_label.pack(side=tk.LEFT, padx=5)
        #
        #
        #+++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++#
        #+++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++#
        #                       Procesamiento de imágenes                               #
        #                       Columna Derecha: Fila 3                                 #
        #+++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++#
        #+++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++#
        #
        ###################################################################################
        ##########      Agrupación en Contorno 2da y 3ra fila de botones       ############
        ###################################################################################
        #                                       #
        # Frame para agrupar las filas          #
        Frame_Proceso_Imagen = tk.LabelFrame(   # Crear un recuadro
            self.button_frame_bottom,           # Frame contenedor
            text="Procesamiento de Imagen",     # Título del recuadro
            padx=10,                            # Ajustar el espaciado externo
            pady=0,                             # Ajustar el espaciado interno
            labelanchor="nw",                   # Alinear la etiqueta en la parte superior
            width=630,                          # Ancho fijo del recuadro
            height=140,                         # Alto fijo del recuadro
            font=("Arial", 10)                  # Establecer la fuente en negrita
        )                                       #
        Frame_Proceso_Imagen.pack_propagate(False)  # Deshabilitar la redimensión automática
        Frame_Proceso_Imagen.pack(side=tk.TOP, anchor="w", padx=5, pady=0)
        #
        #
        #####################################################################################
        #       Configuración de las columas y filas dentro del Frame_Proceso_Imagen        #
        ########********************************************************************#########
        # Crear un contenedor horizontal para las dos columnas
        contenedor_columnas = tk.Frame(Frame_Proceso_Imagen)
        contenedor_columnas.pack(fill="x", expand=True)
        # Columna izquierda: controles básicos
        col_izquierda = tk.Frame(contenedor_columnas, width=460, height=140)
        col_izquierda.pack_propagate(False)
        col_izquierda.pack(side=tk.LEFT, padx=5, pady=5)
        # Columna derecha: bloque de segmentación
        col_derecha = tk.Frame(contenedor_columnas, width=170, height=140)
        col_derecha.pack_propagate(False)
        col_derecha.pack(side=tk.LEFT, padx=5, pady=5)
        #####################################################################################
        #
        # ---------------- Fila superior: Reset + sliders ----------------
        fila_superior = tk.Frame(col_izquierda)
        fila_superior.pack(side=tk.TOP, pady=(0, 5), anchor="w")

        # Botón Reiniciar imagen
        btn_reset = tk.Button(fila_superior, text="Reiniciar\nimagen", command=self.reset_image)
        btn_reset.pack(side=tk.LEFT, padx=(0, 5))

        #Insertar espacio horizontal
        tk.Label(fila_superior, text="  ").pack(side=tk.LEFT, padx=5)
        
        # ----------------- INTENSIDAD ------------------
        frame_slider_hist = tk.Frame(fila_superior)
        frame_slider_hist.pack(side=tk.LEFT, padx=(0, 5))
        tk.Label(frame_slider_hist, text="Intensidad").pack(side=tk.TOP)
        self.equalize_value_label = tk.Label(frame_slider_hist, text="0", font=("Arial", 9))
        self.equalize_value_label.pack(side=tk.TOP)
        slider_band_hist = tk.Frame(frame_slider_hist)
        slider_band_hist.pack(side=tk.TOP)
        #
        # Botón "<"
        btn_hist_minus = tk.Canvas(slider_band_hist, width=16, height=15, highlightthickness=0, bd=0)
        btn_hist_minus.pack(side=tk.LEFT, padx=(0, 1))
        btn_hist_minus_btn = tk.Button(btn_hist_minus, text="\u25C0", fg="#696969", bg="#A9A9A9",
                               activebackground="#B0B0B0", relief="sunken", borderwidth=0,
                               font=("Arial", 9), width=2, padx=0,
                               command=lambda: self.adjust_slider(self.slider_equalize_hist, -1, self.update_equalize_hist))
        btn_hist_minus_btn.bind("<ButtonPress-1>", lambda e: self.start_adjusting(self.slider_equalize_hist, -1, self.update_equalize_hist))
        btn_hist_minus_btn.bind("<ButtonRelease-1>", lambda e: self.stop_adjusting())
        btn_hist_minus.create_window(8, 7, window=btn_hist_minus_btn, anchor="center")
        #
        # Slider
        self.slider_equalize_hist = tk.Scale(slider_band_hist, from_=0, to=100, orient=tk.HORIZONTAL,
                                     command=self.update_equalize_hist, sliderlength=20, width=15,
                                     showvalue=False, length=60, highlightthickness=0, borderwidth=1,
                                     troughcolor="#A9A9A9")
        self.slider_equalize_hist.set(0)
        self.slider_equalize_hist.pack(side=tk.LEFT)
        self.bind_slider_trough(self.slider_equalize_hist, self.update_equalize_hist)
        #
        # Botón ">"
        btn_hist_plus = tk.Canvas(slider_band_hist, width=16, height=15, highlightthickness=0, bd=0)
        btn_hist_plus.pack(side=tk.LEFT, padx=(1, 0))
        btn_hist_plus_btn = tk.Button(btn_hist_plus, text="\u25B6", fg="#696969", bg="#A9A9A9",
                              activebackground="#B0B0B0", relief="sunken", borderwidth=0,
                              font=("Arial", 9), width=2, padx=0,
                              command=lambda: self.adjust_slider(self.slider_equalize_hist, +1, self.update_equalize_hist))
        btn_hist_plus_btn.bind("<ButtonPress-1>", lambda e: self.start_adjusting(self.slider_equalize_hist, +1, self.update_equalize_hist))
        btn_hist_plus_btn.bind("<ButtonRelease-1>", lambda e: self.stop_adjusting())
        btn_hist_plus.create_window(8, 7, window=btn_hist_plus_btn, anchor="center")
        #
        #Insertar espacio horizontal
        tk.Label(fila_superior, text="  ").pack(side=tk.LEFT, padx=10)
        #
        # ----------------- CONTRASTE -------------------
        frame_slider_contrast = tk.Frame(fila_superior)
        frame_slider_contrast.pack(side=tk.LEFT, padx=(0, 5))
        tk.Label(frame_slider_contrast, text="Contraste").pack(side=tk.TOP)
        self.contrast_value_label = tk.Label(frame_slider_contrast, text="0", font=("Arial", 9))
        self.contrast_value_label.pack(side=tk.TOP)
        slider_band_contrast = tk.Frame(frame_slider_contrast)
        slider_band_contrast.pack(side=tk.TOP)
        #
        # Botón "<"
        btn_contrast_minus = tk.Canvas(slider_band_contrast, width=16, height=15, highlightthickness=0, bd=0)
        btn_contrast_minus.pack(side=tk.LEFT, padx=(0, 1))
        btn_contrast_minus_btn = tk.Button(btn_contrast_minus, text="\u25C0", fg="#696969", bg="#A9A9A9",
                                   activebackground="#B0B0B0", relief="sunken", borderwidth=0,
                                   font=("Arial", 9), width=2, padx=0,
                                   command=lambda: self.adjust_slider(self.slider_contrast, -1, self.update_contrast))
        btn_contrast_minus_btn.bind("<ButtonPress-1>", lambda e: self.start_adjusting(self.slider_contrast, -1, self.update_contrast))
        btn_contrast_minus_btn.bind("<ButtonRelease-1>", lambda e: self.stop_adjusting())
        btn_contrast_minus.create_window(8, 7, window=btn_contrast_minus_btn, anchor="center")
        #
        # Slider
        self.slider_contrast = tk.Scale(slider_band_contrast, from_=-100, to=100, orient=tk.HORIZONTAL,
                                command=self.update_contrast, sliderlength=20, width=15,
                                showvalue=False, length=60, highlightthickness=0, borderwidth=1,
                                troughcolor="#A9A9A9")
        self.slider_contrast.set(0)
        self.slider_contrast.pack(side=tk.LEFT)
        self.bind_slider_trough(self.slider_contrast, self.update_contrast)
        #
        # Botón ">"
        btn_contrast_plus = tk.Canvas(slider_band_contrast, width=16, height=15, highlightthickness=0, bd=0)
        btn_contrast_plus.pack(side=tk.LEFT, padx=(1, 0))
        btn_contrast_plus_btn = tk.Button(btn_contrast_plus, text="\u25B6", fg="#696969", bg="#A9A9A9",
                                  activebackground="#B0B0B0", relief="sunken", borderwidth=0,
                                  font=("Arial", 9), width=2, padx=0,
                                  command=lambda: self.adjust_slider(self.slider_contrast, +1, self.update_contrast))
        btn_contrast_plus_btn.bind("<ButtonPress-1>", lambda e: self.start_adjusting(self.slider_contrast, +1, self.update_contrast))
        btn_contrast_plus_btn.bind("<ButtonRelease-1>", lambda e: self.stop_adjusting())
        btn_contrast_plus.create_window(8, 7, window=btn_contrast_plus_btn, anchor="center")

        #Insertar espacio horizontal
        tk.Label(fila_superior, text="  ").pack(side=tk.LEFT, padx=5)
        
        # Contenedor para botones de patrón y marcar
        contenedor_patron_marcar = tk.Frame(fila_superior)
        contenedor_patron_marcar.pack(side=tk.LEFT, padx=5, pady=0)

        self.btn_marcar = tk.Button(contenedor_patron_marcar, text="Seleccionar", height=1, command=self.iniciar_marcado_manual)
        self.btn_marcar.pack(side=tk.TOP, anchor='n', pady=0)
        self.agregar_tooltip(self.btn_marcar, "Presiona para dibujar un patrón sobre\nla imagen. Después presione 'Buscar'")

        self.btn_buscar = tk.Button(contenedor_patron_marcar, text="Buscar", height=1, command=self.detectar_por_patrón_manual, state=tk.DISABLED)
        self.btn_buscar.pack(side=tk.TOP, anchor='n', pady=0)



        # ---------------- Fila inferior: Otros botones ----------------
        fila_inferior = tk.Frame(col_izquierda)
        fila_inferior.pack(side=tk.TOP, pady=(5, 0), anchor="w")
        
#        btn_evaluar = tk.Button(fila_inferior, text="Evaluar detección", height=15, command=self.evaluar_deteccion)
#        btn_evaluar.pack(side=tk.LEFT, padx=(5, 0), ipady=5)

        btn_invert_colors = tk.Button(fila_inferior, text="Invertir color", command=self.invert_colors)
        btn_invert_colors.pack(side=tk.LEFT, padx=20)

        btn_gray_scale = tk.Button(fila_inferior, text="Imagen gris", command=self.convert_to_grayscale)
        btn_gray_scale.pack(side=tk.LEFT, padx=15)

        btn_otsu = tk.Button(fila_inferior, text="Imagen binaria", command=self.apply_otsu_threshold)
        btn_otsu.pack(side=tk.LEFT, padx=15)
#
#        self.btn_detectar_candidatos = tk.Button(
#            fila_inferior, 
#            text="Detectar candidatos", 
#            height=1, 
#            command=self.detectar_candidatos_automaticamente
#        )
#        self.btn_detectar_candidatos.pack(side=tk.TOP, anchor="n", pady=(5, 2))





        # =================== BLOQUE DE SEGMENTACIÓN EN COLUMNA DERECHA ===================
        frame_segmentacion = tk.Frame(col_derecha)
        frame_segmentacion.pack(side=tk.TOP, pady=(0, 2)) 
        tk.Label(frame_segmentacion, text="Segmentar imagen").pack(side=tk.TOP)

        self.segment_menu_button = tk.Menubutton(
            frame_segmentacion,
            text="Segmentar color \u25BC",
            relief=tk.RAISED,
            direction="below",
            width=28,
            font=("Arial", 10),
            height=1
        )
        self.segment_menu_button.pack(side=tk.TOP, pady=(2, 5))

        # Menu desplegable para segmentación
        self.segment_menu = tk.Menu(self.segment_menu_button, tearoff=0)
        self.segment_menu_button.config(menu=self.segment_menu)
        self.segment_menu.add_command(label="Segmentar x color", command=self.iniciar_color_segmentacion)
#        self.segment_menu.add_command(label="Blanco y negro", command=self.iniciar_otsu_segmentacion)
        self.segment_menu.add_command(label="Separar objetos", command=self.iniciar_watershed_segmentacion)
        self.segment_menu.add_command(label="Colores similares", command=self.preparar_kmeans)

        self.frame_k_entry = tk.Frame(frame_segmentacion)
        self.k_label = tk.Label(self.frame_k_entry, text="K:")
        self.k_entry = tk.Entry(self.frame_k_entry, width=3)
        self.k_entry.insert(0, "2")
        self.k_entry.config(state="disabled")
        self.k_entry.bind("<Return>", self.on_enter_k)
        self.k_label.pack(side=tk.LEFT, padx=(0, 2))
        self.k_entry.pack(side=tk.LEFT)
        self.frame_k_entry.pack(side=tk.TOP, pady=(2, 2))
        self.frame_k_entry.pack_forget()

        self.k_hint_label = tk.Label(
            frame_segmentacion,
            text="Número de colores \n para segmentar",
            font=("Arial", 8),
            fg="gray25"
        )
        self.k_hint_label.pack(side=tk.TOP)
        self.k_hint_label.pack_forget()

        self.color_buttons_frame = tk.Frame(frame_segmentacion)
        self.color1_button = tk.Button(
            self.color_buttons_frame,
            text="Color 1",
            state=tk.DISABLED,
            command=self.confirm_color1,
            width=6,
            height=1,
            font=("Arial", 8),
            relief=tk.SUNKEN
        )
        self.color1_button.pack(side=tk.LEFT, padx=2)
        self.color2_button = tk.Button(
            self.color_buttons_frame,
            text="Color 2",
            state=tk.DISABLED,
            command=self.confirm_color2,
            width=6,
            height=1,
            font=("Arial", 8),
            relief=tk.SUNKEN
        )
        self.color2_button.pack(side=tk.LEFT, padx=2)
        self.color_buttons_frame.pack(side=tk.TOP, pady=(2, 2))
        self.color_buttons_frame.pack_forget()

        self.color_hint_label = tk.Label(
            frame_segmentacion,
            text="Seleccione un color\ny presione el botón",
            font=("Arial", 8),
            fg="gray25"
        )
        self.color_hint_label.pack(side=tk.TOP, pady=(2, 0))
        self.color_hint_label.pack_forget()
        #
        #
        #
        ###################################################################################
        #*********              FRAME: Parámetros de contorno                **************
        ###################################################################################
        Frame_Parametros_Contorno = tk.LabelFrame(
            self.button_frame_bottom,           # Frame contenedor
            text="Parámetros de contorno",      # Título del recuadro
            padx=10,                            # Ajustar el espaciado externo
            pady=0,                             # Ajustar el espaciado interno
            labelanchor="nw",                   # Alinear la etiqueta en la parte superior
            font=("Arial", 10),                 # Establecer la fuente en negrita    
            width=630,                          # Ancho fijo del recuadro
            height=170                          # Alto fijo del recuadro    
        )                                       #
        Frame_Parametros_Contorno.pack_propagate(False) # Deshabilitar la redimensión automática
        Frame_Parametros_Contorno.pack(side=tk.TOP, anchor="w", padx=5, pady=0)
        #
        ###################################################################################
        # Fila 1: Deslizadores
        ###################################################################################
        fila_4_frame = tk.Frame(Frame_Parametros_Contorno)
        fila_4_frame.pack(side=tk.TOP, fill="x", pady=5, anchor="nw")

        slider_height = 15       # Altura del deslizador
        slider_Longitud = 55     # Longitud del deslizador


        #---------------------- Frame para Bordes intensidad -----------------------
        #
        frame_param1 = tk.Frame(fila_4_frame)
        frame_param1.pack(side=tk.LEFT, padx=14)
        tk.Label(frame_param1, text="Bordes\nIntensidad").pack(side=tk.TOP, anchor="center")
        self.param1_value_label = tk.Label(frame_param1, text="50", font=("Arial", 9))
        self.param1_value_label.pack(side=tk.TOP)
        slider_band_param1 = tk.Frame(frame_param1, height=slider_height)
        slider_band_param1.pack(side=tk.TOP)

        # Botón "<"
        btn_param1_minus = tk.Canvas(slider_band_param1, width=16, height=slider_height, highlightthickness=0, bd=0)
        btn_param1_minus.pack(side=tk.LEFT, padx=(0, 1))  # margen mínimo
        btn_param1_minus_btn = tk.Button(
            btn_param1_minus,
            text="\u25C0",  # Flecha izquierda
            fg="#696969",
            bg="#A9A9A9",
            activebackground="#B0B0B0",
            relief="sunken",
            borderwidth=0,
            font=("Arial", 9),
            width=2,
            padx=0,
            command=lambda: self.adjust_slider(self.param1_slider, -1, self.update_param1)
        )
        btn_param1_minus_btn.bind("<ButtonPress-1>", lambda e: self.start_adjusting(self.param1_slider, -1, self.update_param1))
        btn_param1_minus_btn.bind("<ButtonRelease-1>", lambda e: self.stop_adjusting())
        btn_param1_minus.create_window(8, slider_height // 2, window=btn_param1_minus_btn, anchor="center")
        #
        # Deslizador central
        self.param1_slider = tk.Scale(
            slider_band_param1,
            from_=1, to=200,
            orient=tk.HORIZONTAL,
            command=self.update_param1,
            sliderlength=20,
            width=slider_height,
            showvalue=False,
            length=slider_Longitud,
            highlightthickness=0,
            borderwidth=1,
            troughcolor="#A9A9A9"
        )
        self.param1_slider.set(50)
        self.param1_slider.pack(side=tk.LEFT)
        self.bind_slider_trough(self.param1_slider, self.update_param1)
        #
        # Botón ">"
        btn_param1_plus = tk.Canvas(slider_band_param1, width=16, height=slider_height, highlightthickness=0, bd=0)
        btn_param1_plus.pack(side=tk.LEFT, padx=(1, 0))  # margen mínimo
        btn_param1_plus_btn = tk.Button(
            btn_param1_plus,
            text="\u25B6",  # Flecha derecha
            fg="#696969",
            bg="#A9A9A9",
            activebackground="#B0B0B0",
            relief="sunken",
            borderwidth=0,
            font=("Arial", 9),
            width=2,
            padx=0,
            command=lambda: self.adjust_slider(self.param1_slider, +1, self.update_param1)
        )
        btn_param1_plus_btn.bind("<ButtonPress-1>", lambda e: self.start_adjusting(self.param1_slider, +1, self.update_param1))
        btn_param1_plus_btn.bind("<ButtonRelease-1>", lambda e: self.stop_adjusting())
        btn_param1_plus.create_window(8, slider_height // 2, window=btn_param1_plus_btn, anchor="center")


        #---------------------- Frame para Bordes Canny -------------------------
        #---------------------- Frame para Bordes Umbral ------------------------
        #
        frame_param2 = tk.Frame(fila_4_frame)
        frame_param2.pack(side=tk.LEFT, padx=16)
        tk.Label(frame_param2, text="Bordes\nUmbral").pack(side=tk.TOP, anchor="center")
        self.param2_value_label = tk.Label(frame_param2, text="30", font=("Arial", 9))
        self.param2_value_label.pack(side=tk.TOP)
        slider_band_param2 = tk.Frame(frame_param2, height=slider_height)
        slider_band_param2.pack(side=tk.TOP)

        # Botón "<"
        btn_param2_minus = tk.Canvas(slider_band_param2, width=16, height=slider_height, highlightthickness=0, bd=0)
        btn_param2_minus.pack(side=tk.LEFT, padx=(0, 1))
        btn_param2_minus_btn = tk.Button(
            btn_param2_minus,
            text="\u25C0",  # Flecha izquierda
            fg="#696969",
            bg="#A9A9A9",
            activebackground="#B0B0B0",
            relief="sunken",
            borderwidth=0,
            font=("Arial", 9),
            width=2,
            padx=0,
            command=lambda: self.adjust_slider(self.param2_slider, -1, self.update_param2)
        )
        btn_param2_minus_btn.bind("<ButtonPress-1>", lambda e: self.start_adjusting(self.param2_slider, -1, self.update_param2))
        btn_param2_minus_btn.bind("<ButtonRelease-1>", lambda e: self.stop_adjusting())
        btn_param2_minus.create_window(8, slider_height // 2, window=btn_param2_minus_btn, anchor="center")
        #
        # Deslizador param2
        self.param2_slider = tk.Scale(
            slider_band_param2,
            from_=1, to=200,
            orient=tk.HORIZONTAL,
            command=self.update_param2,
            sliderlength=20,
            width=slider_height,
            showvalue=False,
            length=slider_Longitud,
            highlightthickness=0,
            borderwidth=1,
            troughcolor="#A9A9A9"
        )
        self.param2_slider.set(30)
        self.param2_slider.pack(side=tk.LEFT)
        self.bind_slider_trough(self.param2_slider, self.update_param2)
        #
        # Botón ">"
        btn_param2_plus = tk.Canvas(slider_band_param2, width=16, height=slider_height, highlightthickness=0, bd=0)
        btn_param2_plus.pack(side=tk.LEFT, padx=(1, 0))
        btn_param2_plus_btn = tk.Button(
            btn_param2_plus,
            text="\u25B6",  # Flecha derecha
            fg="#696969",
            bg="#A9A9A9",
            activebackground="#B0B0B0",
            relief="sunken",
            borderwidth=0,
            font=("Arial", 9),
            width=2,
            padx=0,
            command=lambda: self.adjust_slider(self.param2_slider, +1, self.update_param2)
        )
        btn_param2_plus_btn.bind("<ButtonPress-1>", lambda e: self.start_adjusting(self.param2_slider, +1, self.update_param2))
        btn_param2_plus_btn.bind("<ButtonRelease-1>", lambda e: self.stop_adjusting())
        btn_param2_plus.create_window(8, slider_height // 2, window=btn_param2_plus_btn, anchor="center")


        #----------------------- Frame para el tamaño del contorno (min_size) ----------------
        #
        frame_min_dist = tk.Frame(fila_4_frame)
        frame_min_dist.pack(side=tk.LEFT, padx=5)
        tk.Label(frame_min_dist, text="Separación-centros").pack(side=tk.TOP, anchor="center")
        # Etiqueta de unidades
        tk.Label(frame_min_dist, textvariable=self.distance_units_var, font=("Arial", 8)).pack(side=tk.TOP)
        # Etiqueta del valor actual
        self.min_dist_value_label = tk.Label(frame_min_dist, text="1", font=("Arial", 9))
        self.min_dist_value_label.pack(side=tk.TOP)
        # Banda del deslizador con botones integrados
        slider_band_min_dist = tk.Frame(frame_min_dist, height=slider_height)
        slider_band_min_dist.pack(side=tk.TOP)

        # Botón "<"
        btn_min_dist_minus = tk.Canvas(slider_band_min_dist, width=16, height=slider_height, highlightthickness=0, bd=0)
        btn_min_dist_minus.pack(side=tk.LEFT, padx=(0, 1))
        btn_min_dist_minus_btn = tk.Button(
            btn_min_dist_minus,
            text="\u25C0",  # Flecha izquierda
            fg="#696969",
            bg="#A9A9A9",
            activebackground="#B0B0B0",
            relief="sunken",
            borderwidth=0,
            font=("Arial", 9),
            width=2,
            padx=0,
            command=lambda: self.adjust_slider(self.min_dist_slider, -1, self.update_min_dist)
        )
        btn_min_dist_minus_btn.bind("<ButtonPress-1>", lambda e: self.start_adjusting(self.min_dist_slider, -1, self.update_min_dist))
        btn_min_dist_minus_btn.bind("<ButtonRelease-1>", lambda e: self.stop_adjusting())
        btn_min_dist_minus.create_window(8, slider_height // 2, window=btn_min_dist_minus_btn, anchor="center")
        #
        # Deslizador
        self.min_dist_slider = tk.Scale(
            slider_band_min_dist,
            from_=1, to=400,
            resolution=0.1,
            orient=tk.HORIZONTAL,
            command=self.update_min_dist,
            sliderlength=20,
            width=slider_height,
            showvalue=False,
            length=slider_Longitud,
            highlightthickness=0,
            borderwidth=1,
            troughcolor="#A9A9A9"
        )
        self.min_dist_slider.set(1)
        self.min_dist_slider.pack(side=tk.LEFT)
        self.bind_slider_trough(self.min_dist_slider, self.update_min_dist)
        #
        # Botón ">"
        btn_min_dist_plus = tk.Canvas(slider_band_min_dist, width=16, height=slider_height, highlightthickness=0, bd=0)
        btn_min_dist_plus.pack(side=tk.LEFT, padx=(1, 0))
        btn_min_dist_plus_btn = tk.Button(
            btn_min_dist_plus,
            text="\u25B6",  # Flecha derecha
            fg="#696969",
            bg="#A9A9A9",
            activebackground="#B0B0B0",
            relief="sunken",
            borderwidth=0,
            font=("Arial", 9),
            width=2,
            padx=0,
            command=lambda: self.adjust_slider(self.min_dist_slider, +1, self.update_min_dist)
        )
        btn_min_dist_plus_btn.bind("<ButtonPress-1>", lambda e: self.start_adjusting(self.min_dist_slider, +1, self.update_min_dist))
        btn_min_dist_plus_btn.bind("<ButtonRelease-1>", lambda e: self.stop_adjusting())
        btn_min_dist_plus.create_window(8, slider_height // 2, window=btn_min_dist_plus_btn, anchor="center")


        #----------------------- Frame para el tamaño del contorno (min_size) ----------------
        #
        frame_min_radius = tk.Frame(fila_4_frame)
        frame_min_radius.pack(side=tk.LEFT, padx=4)
        # Etiqueta del deslizador
        tk.Label(frame_min_radius, text="Diámetro mín").pack(side=tk.TOP, anchor="center")
        # Etiqueta de unidades
        tk.Label(frame_min_radius, textvariable=self.distance_units_var, font=("Arial", 8)).pack(side=tk.TOP)
        # Etiqueta del valor actual
        self.min_radius_value_label = tk.Label(frame_min_radius, text="1", font=("Arial", 9))
        self.min_radius_value_label.pack(side=tk.TOP)
        # Banda del deslizador + botones
        slider_band_min_radius = tk.Frame(frame_min_radius, height=slider_height)
        slider_band_min_radius.pack(side=tk.TOP)

        # Botón "<"
        btn_min_radius_minus = tk.Canvas(slider_band_min_radius, width=16, height=slider_height, highlightthickness=0, bd=0)
        btn_min_radius_minus.pack(side=tk.LEFT, padx=(0, 1))
        btn_min_radius_minus_btn = tk.Button(
            btn_min_radius_minus,
            text="\u25C0",  # Flecha izquierda
            fg="#696969",
            bg="#A9A9A9",
            activebackground="#B0B0B0",
            relief="sunken",
            borderwidth=0,
            font=("Arial", 9),
            width=2,
            padx=0,
            command=lambda: self.adjust_slider(self.min_radius_slider, -1, self.update_min_radius)
        )
        btn_min_radius_minus_btn.bind("<ButtonPress-1>", lambda e: self.start_adjusting(self.min_radius_slider, -1, self.update_min_radius))
        btn_min_radius_minus_btn.bind("<ButtonRelease-1>", lambda e: self.stop_adjusting())
        btn_min_radius_minus.create_window(8, slider_height // 2, window=btn_min_radius_minus_btn, anchor="center")
        #
        # Deslizador
        self.min_radius_slider = tk.Scale(
            slider_band_min_radius,
            from_=1, to=400,
            resolution=0.1,
            orient=tk.HORIZONTAL,
            command=self.update_min_radius,
            sliderlength=20,
            width=slider_height,
            showvalue=False,
            length=slider_Longitud,
            highlightthickness=0,
            borderwidth=1,
            troughcolor="#A9A9A9"
        )
        self.min_radius_slider.set(1)
        self.min_radius_slider.pack(side=tk.LEFT)
        self.bind_slider_trough(self.min_radius_slider, self.update_min_radius)
        #
        # Botón ">"
        btn_min_radius_plus = tk.Canvas(slider_band_min_radius, width=16, height=slider_height, highlightthickness=0, bd=0)
        btn_min_radius_plus.pack(side=tk.LEFT, padx=(1, 0))
        btn_min_radius_plus_btn = tk.Button(
            btn_min_radius_plus,
            text="\u25B6",  # Flecha derecha
            fg="#696969",
            bg="#A9A9A9",
            activebackground="#B0B0B0",
            relief="sunken",
            borderwidth=0,
            font=("Arial", 9),
            width=2,
            padx=0,
            command=lambda: self.adjust_slider(self.min_radius_slider, +1, self.update_min_radius)
        )
        btn_min_radius_plus_btn.bind("<ButtonPress-1>", lambda e: self.start_adjusting(self.min_radius_slider, +1, self.update_min_radius))
        btn_min_radius_plus_btn.bind("<ButtonRelease-1>", lambda e: self.stop_adjusting())
        btn_min_radius_plus.create_window(8, slider_height // 2, window=btn_min_radius_plus_btn, anchor="center")


        #------------------------ Frame para el tamaño del contorno (max_size) ----------------
        #
        frame_max_radius = tk.Frame(fila_4_frame)
        frame_max_radius.pack(side=tk.LEFT, padx=22)
        # Etiqueta principal
        tk.Label(frame_max_radius, text="Diámetro máx").pack(side=tk.TOP, anchor="center")
        # Etiqueta de unidades
        tk.Label(frame_max_radius, textvariable=self.distance_units_var, font=("Arial", 8)).pack(side=tk.TOP)
        # Valor actual del deslizador
        self.max_radius_value_label = tk.Label(frame_max_radius, text="1", font=("Arial", 9))
        self.max_radius_value_label.pack(side=tk.TOP)
        # Banda de control (slider + botones)
        slider_band_max_radius = tk.Frame(frame_max_radius, height=slider_height)
        slider_band_max_radius.pack(side=tk.TOP)

        # Botón "<"
        btn_max_radius_minus = tk.Canvas(slider_band_max_radius, width=16, height=slider_height, highlightthickness=0, bd=0)
        btn_max_radius_minus.pack(side=tk.LEFT, padx=(0, 1))
        btn_max_radius_minus_btn = tk.Button(
            btn_max_radius_minus,
            text="\u25C0",  # Flecha izquierda
            fg="#696969",
            bg="#A9A9A9",
            activebackground="#B0B0B0",
            relief="sunken",
            borderwidth=0,
            font=("Arial", 9),
            width=2,
            padx=0,
            command=lambda: self.adjust_slider(self.max_radius_slider, -1, self.update_max_radius)
        )
        btn_max_radius_minus_btn.bind("<ButtonPress-1>", lambda e: self.start_adjusting(self.max_radius_slider, -1, self.update_max_radius))
        btn_max_radius_minus_btn.bind("<ButtonRelease-1>", lambda e: self.stop_adjusting())
        btn_max_radius_minus.create_window(8, slider_height // 2, window=btn_max_radius_minus_btn, anchor="center")
        #
        # Deslizador maxRadius
        self.max_radius_slider = tk.Scale(
            slider_band_max_radius,
            from_=1, to=400,
            resolution=0.1,
            orient=tk.HORIZONTAL,
            command=self.update_max_radius,
            sliderlength=20,
            width=slider_height,
            showvalue=False,
            length=slider_Longitud,
            highlightthickness=0,
            borderwidth=1,
            troughcolor="#A9A9A9"
        )
        self.max_radius_slider.set(1)
        self.max_radius_slider.pack(side=tk.LEFT)
        self.bind_slider_trough(self.max_radius_slider, self.update_max_radius)
        #
        # Botón ">"
        btn_max_radius_plus = tk.Canvas(slider_band_max_radius, width=16, height=slider_height, highlightthickness=0, bd=0)
        btn_max_radius_plus.pack(side=tk.LEFT, padx=(0, 0))
        btn_max_radius_plus_btn = tk.Button(
            btn_max_radius_plus,
            text="\u25B6",  # Flecha derecha
            fg="#696969",
            bg="#A9A9A9",
            activebackground="#B0B0B0",
            relief="sunken",
            borderwidth=0,
            font=("Arial", 9),
            width=2,
            padx=0,
            command=lambda: self.adjust_slider(self.max_radius_slider, +1, self.update_max_radius)
        )
        btn_max_radius_plus_btn.bind("<ButtonPress-1>", lambda e: self.start_adjusting(self.max_radius_slider, +1, self.update_max_radius))
        btn_max_radius_plus_btn.bind("<ButtonRelease-1>", lambda e: self.stop_adjusting())
        btn_max_radius_plus.create_window(8, slider_height // 2, window=btn_max_radius_plus_btn, anchor="center")


        ###################################################################################
        # Fila 2: Botones y selección de contornos
        ###################################################################################
        fila_5_frame = tk.Frame(Frame_Parametros_Contorno)
        fila_5_frame.pack(side=tk.TOP, fill="x", pady=5, anchor="center")

        # Frame para selección de contornos
        self.formas_contours = tk.Frame(fila_5_frame)
        self.formas_contours.pack(side=tk.LEFT, padx=5, pady=0)

        label_title = tk.Label(self.formas_contours, text="Selecciona un contorno:", font=("Arial", 10))
        label_title.pack(side=tk.TOP, anchor="nw", padx=0, pady=(5, 2))
        self.selected_shape = tk.StringVar(value="Círculos")
        rbtn_circles = tk.Radiobutton(
            self.formas_contours,
            text="Círculos",
            variable=self.selected_shape,
            value="Círculos",
            command=lambda: print("Seleccionado: Círculos"),
            font=("Arial", 10)
        )
        rbtn_circles.pack(side=tk.LEFT, anchor="nw", padx=0, pady=0)
        rbtn_others = tk.Radiobutton(
            self.formas_contours,
            text="Otros",
            variable=self.selected_shape,
            value="Otros",
            command=lambda: print("Seleccionado: Otros"),
            font=("Arial", 10)
        )
        rbtn_others.pack(side=tk.LEFT, anchor="w", padx=5, pady=0)
        
        # Botón: Limpiar contornos
        btn_clear_contours = tk.Button(fila_5_frame, text="Limpiar\nimagen", font=("Arial", 9), command=self.clear_contours)
        btn_clear_contours.pack(side=tk.LEFT, padx=5, pady=5)

        # Botón: Aplicar cambios
        apply_changes_button = tk.Button(fila_5_frame, text="Aplicar", command=lambda: self.apply_parameters(
            self.min_dist_slider.get(),
            self.param1_slider.get(),
            self.param2_slider.get(),
            self.min_radius_slider.get(),
            self.max_radius_slider.get()
        ))
        apply_changes_button.pack(side=tk.LEFT, padx=5, pady=5)

        # Botón: Reiniciar valores
        reset_button = tk.Button(fila_5_frame, text="Reiniciar\nvalores", font=("Arial", 9), command=self.reset_sliders_and_image)
        reset_button.pack(side=tk.LEFT, padx=5, pady=5)

        # Botón: Contar contornos
        btn_count_contours = tk.Button(fila_5_frame, text="Contar", command=self.count_contours)
        btn_count_contours.pack(side=tk.LEFT, padx=5, pady=5)
        
        btn_detectar_ref = tk.Button(fila_5_frame, text="Automático", command=self.buscar_candidatos_similares_automaticamente)
        btn_detectar_ref.pack(side=tk.LEFT, padx=5, pady=5)
        # Usar la nueva clase ToolTip
        # Asociar tooltip
        self.agregar_tooltip(btn_detectar_ref, "Ejecuta:\n --> Seleccionar\n --> Buscar\n --> Automático")
    #
    #
    #
    #####################################################################################################
    #####################################################################################################
    #                              Botones y miniaturas de la parte inferior                            #
    #####################################################################################################
    #
    #
    # Función para configurar el frame inferior con miniaturas
    def setup_bottom_frame(self):    
        self.FrameMiniatura = tk.Frame( # Crear un frame para las miniaturas
            self.bottom_frame,          # Contenedor principal
            bg=self.cget("bg"),         # Fondo igual al de la ventana principal
            width=1300, height=160      # Dimensiones ajustadas
        )                               #
        self.FrameMiniatura.grid(row=1, column=0, padx=5, pady=0, sticky="ew")  # Expandir horizontalmente
        self.FrameMiniatura.grid_propagate(False)                               # Evitar que el frame se redimensione
        # Canvas para las miniaturas (permitirá desplazamiento)
        self.thumbnail_canvas = tk.Canvas(
            self.FrameMiniatura,
            width=1300, 
            height=140, 
            bg=self.cget("bg"), 
            highlightthickness=0
        )
        self.thumbnail_canvas.grid(row=0, column=0, sticky="ew")  # Expandir a lo largo del frame

        # Frame interno para las miniaturas dentro del canvas
        self.thumbnail_scroll_frame = tk.Frame(self.thumbnail_canvas, bg=self.cget("bg"))
        self.thumbnail_canvas.create_window((0, 0), window=self.thumbnail_scroll_frame, anchor="nw")

        # Barra de desplazamiento horizontal
        self.thumbnail_scroll_x = tk.Scrollbar(self.FrameMiniatura, orient="horizontal", command=self.thumbnail_canvas.xview, width=12)
        self.thumbnail_scroll_x.grid(row=1, column=0, sticky="ew")  # Debajo del canvas

        # Configurar el desplazamiento del canvas
        self.thumbnail_canvas.configure(xscrollcommand=self.thumbnail_scroll_x.set)

        # Ajustar la región de desplazamiento del canvas cuando el contenido cambia
        self.thumbnail_scroll_frame.bind("<Configure>", lambda _: self.thumbnail_canvas.configure(scrollregion=self.thumbnail_canvas.bbox("all")))

        # Vincular scroll al pasar el mouse por encima
        self.thumbnail_canvas.bind("<Enter>", lambda e: self.bind_mousewheel_to_horizontal_scroll())
        self.thumbnail_canvas.bind("<Leave>", lambda e: self.unbind_all_mousewheel())

        # Configuración adicional de filas y columnas para el layout general
        self.grid_rowconfigure(1, weight=0)     # Evitar que la fila se expanda
        self.grid_columnconfigure(0, weight=1)  # Expandir la columna para que las miniaturas ocupen el ancho completo
    #
    # Función para vincular el desplazamiento del mouse a la barra de desplazamiento horizontal
    def bind_mousewheel_to_horizontal_scroll(self):
        self.bind_all("<MouseWheel>", self.scroll_horizontal_windows)
        self.bind_all("<Button-4>", self.scroll_horizontal_linux)
        self.bind_all("<Button-5>", self.scroll_horizontal_linux)
    def unbind_all_mousewheel(self):
        self.unbind_all("<MouseWheel>")
        self.unbind_all("<Button-4>")
        self.unbind_all("<Button-5>")
    def scroll_horizontal_windows(self, event):
        self.thumbnail_canvas.xview_scroll(-1 * (event.delta // 120), "units")
    def scroll_horizontal_linux(self, event):
        direction = -1 if event.num == 4 else 1
        self.thumbnail_canvas.xview_scroll(direction, "units")
    #
    #
    ##########################################################################################
    ##########################################################################################
    ##########################################################################################
    ########       Funciones de los botones lado izquierdo debajo de la imagen       #########
    ########                                                                         #########
    ##########################################################################################
    ##########################################################################################
    #
    #
    # Función para cargar imágenes desde un directorio
    def load_images(self):
        self.geometry("400x300")  # Tamaño fijo para la ventana principal durante el diálogo
        self.image_directory = filedialog.askdirectory()  # Abrir diálogo para seleccionar directorio       
        if self.image_directory:
            self.display_images(self.image_directory)

    # Función para actualizar el canvas con la imagen actual
    def refresh_images(self):
        if self.image_directory:
            self.display_images(self.image_directory)

    # Función para guardar la imagen procesada que se está mostrando en el canvas
    def save_image(self):
        if not hasattr(self, 'processed_image') or self.processed_image is None:
            messagebox.showwarning("Advertencia", "No hay imagen procesada para guardar.")
            return
        # Configurar cuadro de diálogo para guardar el archivo
        base_name = os.path.basename(self.current_image_path or "imagen_procesada")
        initial_file_name = f"{os.path.splitext(base_name)[0]}_procesada.png"
        file_path = filedialog.asksaveasfilename(
            defaultextension=".png",
            initialfile=initial_file_name,
            filetypes=[
                ("PNG", "*.png"),
                ("JPEG", "*.jpg *.jpeg"),
                ("Bitmap", "*.bmp"),
                ("TIFF", "*.tif *.tiff"),
                ("Todos los archivos", "*.*")
            ],
            initialdir=self.image_directory
        )
        if file_path:
            # Guardar la imagen procesada (ya sea con círculos o contornos)
            cv2.imwrite(file_path, cv2.cvtColor(self.processed_image, cv2.COLOR_RGB2BGR))
            messagebox.showinfo("Imagen guardada", 
#                              f"La imagen procesada se guardó correctamente en:\n{file_path}")
                              f"La imagen procesada se guardó correctamente")
    #
    #
    #
    ##########################################################################################
    ##########################################################################################
    ###################       Funciones de los botones lado derecho       ####################
    ###################                                                   ####################
    ##########################################################################################
    ##########################################################################################
    #
    #
    ##########################################################################################
    #****************************************************************************************#
    ###################             Funciones de los botones            ######################
    ###################                     1ra línea                   ######################
    #****************************************************************************************#
    ##########################################################################################
    #
    # Función para hacer zoom in (acercar)
    def zoom_in(self):
        if self.original_image is None:
            return
        self.save_state()
        self.scale_factor = min(self.scale_factor*1.1, self.max_scale)
        self.update_zoom_display()
        self.redraw_contours()
        self.redraw_mediciones()

    # Función para hacer zoom out (alejar)
    def zoom_out(self):
        if self.original_image is None:
            return
        self.save_state()
        self.scale_factor = max(self.scale_factor/1.1, self.min_scale)
        self.update_zoom_display()
        self.redraw_contours()
        self.redraw_mediciones()

    # Función para aplicar el zoom actual a la imagen
    def apply_zoom(self):
        if self.temp_image is None:
            return
        source_img = self.temp_image
        if isinstance(source_img, Image.Image):
            img_pil = source_img
        else:
            img_pil = Image.fromarray(cv2.cvtColor(source_img, cv2.COLOR_BGR2RGB))
        new_width = int(self.original_width*self.scale_factor)
        new_height = int(self.original_height*self.scale_factor)
        if new_width <= 0 or new_height <= 0:
            messagebox.showwarning("Zoom inválido", "La imagen es demasiado pequeña para mostrar.")
            return
        resized = img_pil.resize((new_width, new_height), Image.Resampling.LANCZOS)
        self.img_tk = ImageTk.PhotoImage(resized)
        self.x_offset, self.y_offset = self.calculate_centered_coordinates(new_width, new_height)
        # Eliminar solo la imagen, mantener objetos como contornos
        self.canvas.delete("image")
        # Insertar nueva imagen con etiqueta "image"
        self.canvas.create_image(self.x_offset, self.y_offset, anchor="nw", image=self.img_tk, tags="image")
        self.canvas.image = self.img_tk
        self.canvas.config(scrollregion=(0, 0, new_width, new_height))
        # Reescalar los objetos del canvas (líneas, rectángulos, contornos)
        self._update_canvas_drawings()


    # Función para actualizar la conversión de zoom
    def actualizar_conversion_zoom(self):
        pix_val = self.ValorPixel.get()
        dist_val = self.ValorDistancia.get()
        # Validar que no haya división por cero
        if pix_val > 0 and dist_val > 0 and self.scale_factor > 0:
            self.ValorConversion = dist_val/(pix_val*self.scale_factor)
            self.conversion_label.config(text=f"{self.ValorConversion:.2f}")
            nuevo_limite = 400*self.ValorConversion
        
            # Guardar valores actuales para no sobrescribir
            min_radius_val = self.min_radius_slider.get()
            max_radius_val = self.max_radius_slider.get()
            min_dist_val = self.min_dist_slider.get()
            # Actualizar límites de los sliders sin cambiar sus valores
            self.min_radius_slider.config(to=nuevo_limite)
            self.max_radius_slider.config(to=nuevo_limite)
            self.min_dist_slider.config(to=nuevo_limite)
            # Actualizar etiquetas visuales sin modificar valores del usuario
            self.update_min_radius(min_radius_val)
            self.update_max_radius(max_radius_val)
            self.update_min_dist(min_dist_val)
        else:
            print("Conversión no actualizada: ValorPixel, ValorDistancia o escala inválidos.")


    # Función para convertir coordenadas visibles a coordenadas originales
    def get_original_coordinates(self, x, y):
        # Ajustar desplazamiento y escala
        x_canvas = self.canvas.canvasx(x) - self.x_offset
        y_canvas = self.canvas.canvasy(y) - self.y_offset
        orig_x = x_canvas/self.scale_factor
        orig_y = y_canvas/self.scale_factor
        return orig_x, orig_y


    # Función para calcular las coordenadas centralizadas de la imagen
    def update_zoom_display(self):
        if self.temp_image is None:
            return
        source_img = self.temp_image
        if isinstance(source_img, Image.Image):
            img_pil = source_img
        else:
            img_rgb = cv2.cvtColor(source_img, cv2.COLOR_BGR2RGB)
            img_pil = Image.fromarray(img_rgb)
        new_width = int(self.original_width*self.scale_factor)
        new_height = int(self.original_height*self.scale_factor)
        img_resized = img_pil.resize((new_width, new_height), Image.Resampling.LANCZOS)
        img_tk = ImageTk.PhotoImage(img_resized)

        self.x_offset, self.y_offset = self.calculate_centered_coordinates(new_width, new_height)

        # Eliminar solo la imagen previa, no los contornos
        self.canvas.delete("image")
        # Asignar etiqueta "image" al nuevo objeto de imagen
        self.canvas.create_image(self.x_offset, self.y_offset, anchor="nw", image=img_tk, tags="image")
        self.canvas.image = img_tk
        self.canvas.config(scrollregion=(0, 0, new_width, new_height))
        # Reescalar objetos dibujados como contornos
        self._update_canvas_drawings()


    # Función para calcular las coordenadas centralizadas de la imagen
    def update_image(self):
        if self.original_image is None:
            return  # Verificar si hay imagen cargada
        # Convertir imagen de OpenCV (BGR) a PIL (RGB)
        new_width = int(self.original_width*self.scale_factor)
        new_height = int(self.original_height*self.scale_factor)
        resized_image = self.original_image.resize((new_width, new_height), Image.Resampling.LANCZOS)
        self.image = ImageTk.PhotoImage(resized_image)
        # Calcular coordenadas centralizadas
        x, y = self.calculate_centered_coordinates(new_width, new_height)
        # Mostrar imagen redimensionada en el canvas
        self.canvas.delete("all")
        self.canvas.create_image(x, y, image=self.image, anchor="nw", tag="image")
        # Actualizar área de desplazamiento
        self.canvas.config(scrollregion=self.canvas.bbox("all"))
        self.canvas.image = self.image  # Mantener referencia


    # Función que ajusta las coordenadas de un objeto en el canvas según el zoom y el desplazamiento
    def _rescale_canvas_item(self, item_id):
        original_coords = self.canvas.coords(item_id)  # Coordenadas actuales
        # Ajustar coordenadas al estado original antes del zoom
        scaled_coords = [
            (coord - self.x_offset)*self.scale_factor + self.x_offset if idx % 2 == 0 else
            (coord - self.y_offset)*self.scale_factor + self.y_offset
            for idx, coord in enumerate(original_coords)
        ]
        self.canvas.coords(item_id, *scaled_coords)


    # Función para calcular las coordenadas centralizadas de la imagen
    def _get_image_offsets(self):
        img_width = int(self.original_width*self.scale_factor)
        img_height = int(self.original_height*self.scale_factor)
        return self.calculate_centered_coordinates(img_width, img_height)


    # Función para restablecer la imagen original
    def _update_canvas_drawings(self):
        if self.line_id:
            self._rescale_canvas_item(self.line_id)
        if self.rect_id:
            self._rescale_canvas_item(self.rect_id)
        if hasattr(self, 'contour_canvas_ids'):
            for obj_id in self.contour_canvas_ids:
                self._rescale_canvas_item(obj_id)


    # Función para guardar el estado actual de la imagen y los parámetros
    def save_state(self):
        if self.temp_image is not None:
            # Extraer contenido de la tabla
            tabla_datos = []
            for item in self.results_table.get_children():
                valores = self.results_table.item(item)["values"]
                tabla_datos.append(valores)
            # Guardar el estado actual en la pila de deshacer
            state = {
                'image': self.temp_image.copy(),
                'scale_factor': self.scale_factor,
                'medicion_lineas': self.medicion_lineas.copy(),
                'medicion_rectangulos': self.medicion_rectangulos.copy(),
                'tabla_resultados': tabla_datos,
                'segmentacion_actual': self.segment_menu_button.cget("text"),                
                'sliders': {
                    'equalize_hist': self.slider_equalize_hist.get(),
                    'contrast': self.slider_contrast.get(),
                    'min_radius': self.min_radius_slider.get(),
                    'max_radius': self.max_radius_slider.get(),
                    'min_dist': self.min_dist_slider.get()
                },
                'patron_intensidad_referencia': self.patron_intensidad_referencia.copy() if hasattr(self, 'patron_intensidad_referencia') and self.patron_intensidad_referencia is not None else None,
                'radio_referencia_manual': getattr(self, 'radio_referencia_manual', None)
            }
            self.undo_stack.append(state)
            if getattr(self, 'just_undone', False):
                self.redo_stack.clear()
                self.just_undone = False


    # Función para deshacer el último cambio realizado
    def undo_change(self):
        if not self.undo_stack:
            messagebox.showinfo("Deshacer", "No hay cambios para deshacer.")
            return
        # Indicar que acabamos de hacer undo
        self.just_undone = True
        # Guardar el estado actual en redo_stack
        current_state = {
            'image': self.temp_image.copy(),
            'scale_factor': self.scale_factor,
            'medicion_lineas': self.medicion_lineas.copy(),
            'medicion_rectangulos': self.medicion_rectangulos.copy(),
            'segmentacion_actual': self.segment_menu_button.cget("text"),            
            'sliders': {
                'equalize_hist': self.slider_equalize_hist.get(),
                'contrast': self.slider_contrast.get(),
                'min_radius': self.min_radius_slider.get(),
                'max_radius': self.max_radius_slider.get(),
                'min_dist': self.min_dist_slider.get()
            }
        }
        self.redo_stack.append(current_state)
        # Restaurar el estado anterior
        prev_state = self.undo_stack.pop()
        self.temp_image = prev_state['image']
        self.scale_factor = prev_state.get('scale_factor', 1.0)
        self.medicion_lineas = prev_state.get('medicion_lineas', [])
        self.medicion_rectangulos = prev_state.get('medicion_rectangulos', [])
        # 
        sliders = prev_state['sliders']
        self.slider_equalize_hist.set(sliders['equalize_hist'])
        self.slider_contrast.set(sliders['contrast'])
        self.min_radius_slider.set(sliders['min_radius'])
        self.max_radius_slider.set(sliders['max_radius'])
        self.min_dist_slider.set(sliders['min_dist'])
        # Aplicar los cambios
        self.update_zoom_display()
        self.sync_sliders(sliders)
        self.redraw_contours()
        self.redraw_mediciones()

        # Restaurar estado del menú de segmentación
        segmentacion = prev_state.get('segmentacion_actual', "Segmentar color \u25BC")
        self.segment_menu_button.config(text=segmentacion)
        # Restablecer visibilidad de los controles según el método
        self.ocultar_botones_color()
        self.ocultar_campo_k()
        self.ocultar_instruccion_color()
        if "Color" in segmentacion:
            self.color_buttons_frame.pack(side=tk.TOP, pady=(2, 2))
            self.color1_button.pack(side=tk.LEFT, padx=2)
            self.color2_button.pack(side=tk.LEFT, padx=2)
            self.color1_button.config(state=tk.DISABLED, relief=tk.SUNKEN)
            self.color2_button.config(state=tk.DISABLED, relief=tk.SUNKEN)
            self.color_hint_label.pack(side=tk.TOP)
        elif "K-means" in segmentacion:
            self.frame_k_entry.pack(side=tk.TOP, pady=(2, 2))
            self.k_hint_label.pack(side=tk.TOP)
            self.k_entry.config(state="normal")


    # Función para rehacer el último cambio deshecho
    def redo_change(self):
        if not self.redo_stack:
            messagebox.showinfo("Rehacer", "No hay cambios para rehacer.")
            return
        # Guardar el estado actual en la pila de deshacer
        current_state = {
            'image': self.temp_image.copy(),
            'scale_factor': self.scale_factor,
            'medicion_lineas': self.medicion_lineas.copy(),
            'medicion_rectangulos': self.medicion_rectangulos.copy(),
            'segmentacion_actual': self.segment_menu_button.cget("text"),
            'sliders': {
                'equalize_hist': self.slider_equalize_hist.get(),
                'contrast': self.slider_contrast.get(),
                'min_radius': self.min_radius_slider.get(),
                'max_radius': self.max_radius_slider.get(),
                'min_dist': self.min_dist_slider.get()
            }
        }
        self.undo_stack.append(current_state)
        # Restaurar el estado siguiente
        next_state = self.redo_stack.pop()
        self.temp_image = next_state['image']
        self.scale_factor = next_state.get('scale_factor', 1.0)
        self.medicion_lineas = next_state.get('medicion_lineas', [])
        self.medicion_rectangulos = next_state.get('medicion_rectangulos', [])
        #
        sliders = next_state['sliders']
        self.slider_equalize_hist.set(sliders['equalize_hist'])
        self.slider_contrast.set(sliders['contrast'])
        self.min_radius_slider.set(sliders['min_radius'])
        self.max_radius_slider.set(sliders['max_radius'])
        self.min_dist_slider.set(sliders['min_dist'])
        # Aplicar los cambios
        self.update_zoom_display()
        self.sync_sliders(sliders)
        self.redraw_contours()
        self.redraw_mediciones()
        # Restaurar estado del menú de segmentación
        segmentacion = next_state.get('segmentacion_actual', "Segmentar color \u25BC")
        self.segment_menu_button.config(text=segmentacion)
        # Restablecer visibilidad de los controles según el método
        self.ocultar_botones_color()
        self.ocultar_campo_k()
        self.ocultar_instruccion_color()
        if "Color" in segmentacion:
            self.color_buttons_frame.pack(side=tk.TOP, pady=(2, 2))
            self.color1_button.pack(side=tk.LEFT, padx=2)
            self.color2_button.pack(side=tk.LEFT, padx=2)
            self.color1_button.config(state=tk.DISABLED, relief=tk.SUNKEN)
            self.color2_button.config(state=tk.DISABLED, relief=tk.SUNKEN)
            self.color_hint_label.pack(side=tk.TOP)
        elif "K-means" in segmentacion:
            self.frame_k_entry.pack(side=tk.TOP, pady=(2, 2))
            self.k_hint_label.pack(side=tk.TOP)
            self.k_entry.config(state="normal")


    # Función para tomar una foto desde la pestaña activa
    def take_photo(self):
        start_time = time.time()
        active_tab = self.notebook.index(self.notebook.select())
        if active_tab == 0:
            image_data = self.capture_widget(self.canvas_tab)
        elif active_tab == 1:
            image_data = self.capture_widget(self.canvas_tab_temp)
        elif active_tab == 2:
            image_data = self.capture_widget(self.canvas_tab_results)
        elif active_tab == 3:
            image_data = self.capture_widget(self.camera_tab)
        else:
            return
        if image_data is None:
            messagebox.showerror("Error", "No se pudo capturar la imagen.")
            return
        self.current_image = image_data
        file_path = tk.filedialog.asksaveasfilename(
            defaultextension=".png",
            filetypes=[("Archivos PNG", "*.png"), ("Todos los archivos", "*.*")],
            title="Guardar imagen"
        )
        if not file_path:                           # Si no se selecciona un archivo,
            return                                  #
        cv2.imwrite(file_path, self.current_image)  # Guardar la imagen en el archivo seleccionado
        self.load_image(file_path)                  # Cargar la imagen guardada


    # Función para capturar el contenido del canvas y convertirlo en una imagen
    def capture_widget(self, widget):
        # Si el widget no es un Canvas, busca el Canvas dentro de él
        if isinstance(widget, tk.Canvas):
            canvas = widget
        else:
            # Si es un Frame, intenta obtener el Canvas dentro del Frame
            canvas = widget.winfo_children()[0] if widget.winfo_children() else None
        # Si no se encontró un Canvas, muestra un mensaje de error
        if canvas is None or not isinstance(canvas, tk.Canvas):
            messagebox.showerror("Error", "No se encontró un Canvas dentro del widget.")
            return None
        #
        ps = canvas.postscript(colormode='color')               # Usar el método 'postscript' para capturar el contenido del canvas
        img = Image.open(io.BytesIO(ps.encode('utf-8')))        # Convertir la salida del 'postscript' a una imagen usando PIL
        img = cv2.cvtColor(np.array(img), cv2.COLOR_RGB2BGR)    # Convertir la imagen de PIL a un formato de OpenCV (si es necesario)
        return img


    # Función para mostrar un mensaje de ayuda al usuario
    def ayuda_usuario(self):
        # Crear una nueva ventana Toplevel
        ventana_ayuda = tk.Toplevel(self)
        ventana_ayuda.title("Ayuda del sistema")
        ventana_ayuda.geometry("750x600")
        ventana_ayuda.resizable(True, True)

        # Encabezado
        tk.Label(ventana_ayuda, text="Descripción de la interfaz del sistema SICS", font=("Arial", 14, "bold")).pack(pady=(10, 0))
        # Frame con scroll
        frame_texto = tk.Frame(ventana_ayuda)
        frame_texto.pack(fill="both", expand=True, padx=10, pady=10)
        # Scrollbar para el texto
        scroll = tk.Scrollbar(frame_texto)
        scroll.pack(side="right", fill="y")
        # Configurar el texto con scroll
        texto = tk.Text(
            frame_texto,
            wrap="word",
            yscrollcommand=scroll.set,
            font=("Courier New", 12),
            bg="#f9f9f9",
            padx=12,
            pady=10
        )
        texto.pack(side="left", fill="both", expand=True)
        scroll.config(command=texto.yview)
        # Estilo de interlineado
        texto.tag_configure("espaciado", spacing1=4, spacing2=4, spacing3=6)
        # Contenido de ayuda
        contenido = (
        "Guía de botones y funciones principales\n\n"
        "Pestañas de visualización\n"
        "• Imagen temporal: Muestra la imagen actual con los últimos ajustes o procesamiento aplicado.\n"
        "• Imagen original: Visualiza la imagen tal como fue cargada, sin modificaciones.\n"
        "• Cámara: Muestra el video en tiempo real desde la cámara seleccionada y permite capturar imágenes para analizarlas.\n"
        "• Resultados: Presenta una tabla con las mediciones registradas, una gráfica de distribución y estadísticas como promedio y la desviación estándar.\n\n"

        "Parámetros de referencia\n"
        "• Medir referencia: Traza una línea sobre la imagen para establecer la escala entre píxeles y unidades físicas. Se activa cuando el botón está en verde.\n"
        "• Pixeles: Muestra o permite ingresar manualmente la distancia en píxeles de la línea trazada. Se registra cuando el botón está en verde.\n"
        "• Referencia: Permite introducir manualmente la distancia real correspondiente (nm, µm, mm, etc.). Se registra cuando el botón está en verde.\n"
        "• Aplicar: Calcula la equivalencia unidad/píxel. El valor se registra cuando el botón está en rojo.\n"
        "• Longitud: Mide distancias dentro de la imagen utilizando la escala establecida. Se activa cuando el botón está en verde.\n"
        "• Agregar a la tabla: Guarda automáticamente en la tabla las mediciones obtenidas con el trazo activado por el botón <Longitud>. Permanece activo mientras el botón está en azul.\n"
        "• Reiniciar valores: Restablece los valores actuales de longitud y escala a su estado inicial.\n\n"

        "Procesamiento de imagen\n"
        "• Reiniciar imagen: Restaura la imagen procesada a su estado original.\n"
        "• Intensidad: Ajusta la intensidad de la imagen para mejorar contraste interno.\n"
        "• Contraste: Modifica el contraste general de la imagen para resaltar detalles.\n"
        "• Seleccionar: Permite marcar manualmente un patrón de referencia sobre la imagen (por ejemplo, el contorno de una nanopartícula). El usuario traza un círculo que se utilizará como plantilla de búsqueda.\n"
        "• Seleccionar --> Buscar: Tras marcar un patrón con 'Seleccionar', este botón activa una búsqueda por coincidencia de intensidad utilizando la plantilla seleccionada. Se marcan en la imagen todas las regiones similares al patrón.\n"
        "• Segmentar color: Activa la herramienta para seleccionar dos colores utilizados en la segmentación.\n"
        "• Color 1 y Color 2: Confirma y bloquea los colores seleccionados desde la imagen.\n"
        "• Invertir colores: Invierte los colores de la imagen (efecto negativo).\n"
        "• Imagen en grises: Convierte la imagen a escala de grises.\n"
        "• Imagen binaria: Aplica un umbral automático (Otsu) para convertir la imagen en blanco y negro.\n"
        "• Segmentar por color: Activa la herramienta para seleccionar dos colores que se usarán para separar regiones.\n"
        "• Segmentar color --> Color 1 y Color 2: Permiten confirmar y fijar los colores seleccionados desde la imagen.\n"
#        "• Segmentar color --> Blanco y negro automático: Convierte la imagen a blanco y negro sin necesidad de ajustar parámetros.\n"
        "• Segmentar color --> Separar objetos: Útil cuando hay elementos juntos o superpuestos; separa automáticamente los objetos.\n"
        "• Segmentar color --> Colores similares: Agrupa regiones con colores parecidos sin tener que seleccionar manualmente.\n\n"

        "Parámetros de contorno\n"
        "• Bordes Intensidad: Ajusta la sensibilidad de detección de bordes.\n"
        "• Bordes Umbral: Define el umbral mínimo para considerar un borde como válido.\n"
        "• Separación-centros: Establece la distancia mínima entre los centros de los objetos detectados.\n"
        "• Diámetros: Define los valores mínimo y máximo del diámetro de los objetos circulares a detectar.\n"
        "• Selección de contorno: Permite elegir entre detectar Círculos u otras formas irregulares.\n"
        "• Limpiar imagen: Elimina todos los contornos dibujados en la imagen.\n"
        "• Aplicar cambios: Aplica los valores configurados en los deslizadores.\n"
        "• Reiniciar valores: Restaura los parámetros de contorno a sus valores por defecto.\n"
        "• Contar: Ejecuta el análisis para detectar y contabilizar objetos.\n"
        "• Automático: Realiza la búsqueda de contornos similares al patrón seleccionado manualmente mediante la secuencia 'Seleccionar --> Buscar --> Automático'. Si no se ha definido un patrón, utiliza directamente los valores establecidos en los deslizadores (diámetro mínimo/máximo, separación entre centros, intensidad de bordes) para detectar regiones circulares de forma automática.\n\n"

        "Botones de cámara\n"
        "• Cámara: Despliega un menú con opciones para activar o desactivar cámaras conectadas.\n"
        "• Cámara --> Buscar cámaras: Escanea y muestra las cámaras disponibles para su selección.\n"
        "• Tomar foto: Captura la imagen mostrada en la pestaña <Imagen temporal> o desde la cámara seleccionada. La imagen tomada puede guardarse y se visualizará en la pestaña <Imagen temporal>.\n\n"

        "Otros botones\n"
        "• Directorio: Abre la carpeta de trabajo que contiene las imágenes para procesar.\n"
        "• Actualizar: Actualiza las miniaturas de imágenes cargadas desde el directorio.\n"
        "• Guardar imagen: Guarda la imagen procesada.\n"
        "• Limpiar tabla: Elimina todos los registros de la tabla de resultados.\n"
        "• Exportar datos: Guarda los resultados numéricos en un archivo con extensión '.dat'.\n"
        "• Gráfica: Genera un histograma de las mediciones en la pestaña <Resultados> y muestra estadísticas descriptivas como promedio y la desviación estándar.\n"
        )
        texto.insert("1.0", contenido, "espaciado")
        texto.config(state="disabled")
        # Botón para cerrar
        tk.Button(ventana_ayuda, text="Cerrar", command=ventana_ayuda.destroy).pack(pady=5)
    #
    #
    #
    ##########################################################################################
    #****************************************************************************************#
    ###################             Funciones de los botones            ######################
    ###################             Parámetros de referencia            ######################
    #****************************************************************************************#
    ##########################################################################################
    #
    #
    ##########################################################################################
    #*********       Funciones de los botones de Parámetros de referencia        ************#
    #***********************              1ra Fila                    ***********************#
    #*********************************                       ********************************#
    ##########################################################################################
    #
    # Función para mostrar la imagen en pantalla
    def toggle_measurement(self):
        if self.is_measuring_reference or self.is_measuring_rectangle:
            self.disable_measurement()
        else:
            self.enable_measurement()


    # Función para habilitar la medición
    def enable_measurement(self):
        self.is_measuring_reference = True
        self.canvas.bind("<ButtonPress-1>", self.start_line)
        self.canvas.bind("<B1-Motion>", self.draw_line)
        self.canvas.bind("<ButtonRelease-1>", self.finish_line)
        self.is_measuring_rectangle = False
        self.canvas.unbind("<ButtonPress-1>")
        self.canvas.unbind("<B1-Motion>")
        self.canvas.unbind("<ButtonRelease-1>")


    # Función para deshabilitar la medición
    def disable_measurement(self):
        self.is_measuring_reference = False
        self.is_measuring_rectangle = False
        self.canvas.unbind("<ButtonPress-1>")
        self.canvas.unbind("<B1-Motion>")
        self.canvas.unbind("<ButtonRelease-1>")
        self.reset_state()


    # Función para restablecer el estado de líneas y rectángulos
    def reset_state(self):
        self.line_id = None
        self.rect_id = None
        self.start_x = None
        self.start_y = None


    # Función para ajustar las coordenadas de un objeto en el canvas según el zoom
    def adjust_coordinates(self, x_canvas, y_canvas):
        # Ajustar las coordenadas de la imagen con el desplazamiento y el zoom
        adjusted_x = (x_canvas - self.x_offset)/self.scale_factor
        adjusted_y = (y_canvas - self.y_offset)/self.scale_factor
        return adjusted_x, adjusted_y


    # Función para iniciar la medición del trazo de una línea en el canvas
    def start_line(self, event):
        # Guardar el estado actual antes de iniciar la medición
        self.save_state()
        # Obtener coordenadas ajustadas
        self.start_x, self.start_y = self.get_original_coordinates(event.x, event.y)
        # Crear la línea inicial en el canvas (en las coordenadas ajustadas)
        self.line_id = self.canvas.create_line(
            event.x, event.y, event.x, event.y, fill="red", width=2, tags="medicion"
        )


    # Función para actualizar el trazo de la línea mientras se arrastra el mouse
    def draw_line(self, event):
        if self.start_x is None or self.start_y is None:
            return  # Evita trazar si no se ha iniciado correctamente
        # Obtener coordenadas ajustadas para el punto final
        end_x, end_y = self.get_original_coordinates(event.x, event.y)
        # Actualizar la línea en el canvas usando las coordenadas escaladas
        self.canvas.coords(
            self.line_id,
            self.start_x*self.scale_factor + self.x_offset,
            self.start_y*self.scale_factor + self.y_offset,
            end_x*self.scale_factor + self.x_offset,
            end_y*self.scale_factor + self.y_offset
        )


    # Función para redibujar las líneas de medición en el canvas
    def redraw_mediciones(self):
        # Borrar todas las líneas y rectángulos previos
        self.canvas.delete("medicion")
        # Redibujar las líneas de medición almacenadas
        for x0, y0, x1, y1 in self.medicion_lineas:
            self.canvas.create_line(
                x0*self.scale_factor + self.x_offset,
                y0*self.scale_factor + self.y_offset,
                x1*self.scale_factor + self.x_offset,
                y1*self.scale_factor + self.y_offset,
                fill="red", width=2, tags="medicion"
            )
        # Redibujar los rectángulos de medición almacenados
        for x0, y0, x1, y1 in self.medicion_rectangulos:
            self.canvas.create_rectangle(
                x0*self.scale_factor + self.x_offset,
                y0*self.scale_factor + self.y_offset,
                x1*self.scale_factor + self.x_offset,
                y1*self.scale_factor + self.y_offset,
                outline="red", width=2, tags="medicion"
        )


    # Función para finalizar el trazo de la línea y calcula la distancia
    def finish_line(self, event):
        if self.start_x is None or self.start_y is None:
            return  # Evita calcular si no hay inicio válido
        end_x, end_y = self.get_original_coordinates(event.x, event.y)
        # Cálculo de la distancia original (sin considerar el zoom)
        distance = sqrt((end_x - self.start_x) ** 2 + (end_y - self.start_y) ** 2)
        # Ajuste la distancia final según el zoom
        self.MedicionPixeles = distance
        # Actualizar la variable de longitud
        self.pixels_entry.delete(0, tk.END)
        self.pixels_entry.insert(0, f"{distance:.2f}")
        self.realizar_calculo()
        self.save_state()  # Guardar después de medir
        # Inserta el valor en la tabla si el botón agregar medición está activado
        if self.agregar_a_tabla:
            num = len(self.results_table.get_children()) + 1
            self.results_table.insert("", "end", values=(num, f"{self.ValorLongitud.get():.2f}"))
        # Almacenar las coordenadas originales (sin escala)
        self.medicion_lineas.append((self.start_x, self.start_y, end_x, end_y))
        self.line_id = None
        self.start_x, self.start_y = None, None


    # Función para habilitar el modo de dibujo del rectángulo
    def enable_rectangle_mode(self):
        self.canvas.bind("<ButtonPress-1>", self.start_rectangle)
        self.canvas.bind("<B1-Motion>", self.update_rectangle)
        self.canvas.bind("<ButtonRelease-1>", self.finish_rectangle)   


    # Función para dibujar el rectángulo
    def start_rectangle(self, event):
        # Guardar el estado actual antes de iniciar el rectángulo
        self.save_state()
        # Ajustar las coordenadas del inicio del rectángulo
        self.start_x, self.start_y = self.adjust_coordinates(event.x, event.y)
        self.rect_id = self.canvas.create_rectangle(
            event.x, event.y, event.x, event.y, outline="red", width=2, tags="medicion"
        )


    # Función para actualizar las dimensiones del rectángulo mientras se dibuja
    def update_rectangle(self, event):
        end_x, end_y = self.adjust_coordinates(event.x, event.y)
        self.canvas.coords(
            self.rect_id,
            self.start_x*self.scale_factor + self.x_offset,
            self.start_y*self.scale_factor + self.y_offset,
            end_x*self.scale_factor + self.x_offset,
            end_y*self.scale_factor + self.y_offset
        )


    # Función para finalizar el dibujo del rectángulo y actualizar las variables
    def finish_rectangle(self, event):
        end_x, end_y = self.adjust_coordinates(event.x, event.y)
        largo = abs(end_x - self.start_x)  # Distancia horizontal
        ancho = abs(end_y - self.start_y)  # Distancia vertical
        # Ajuste de dimensiones con el factor de zoom
        largo_real = largo/self.scale_factor
        ancho_real = ancho/self.scale_factor
        # Actualizar las variables asociadas
        self.ValorLargo.set(largo_real)
        self.ValorAncho.set(ancho_real)
        # Realizar el cálculo de conversión de acuerdo a las dimensiones
        self.realizar_calculo()
        self.rect_id = None        
        # Almacenar las coordenadas originales del rectángulo
        self.medicion_rectangulos.append((self.start_x, self.start_y, end_x, end_y))


    # Función para dibujar un rectángulo en el canvas  teniendo en cuenta la escala y los desplazamientos
    def draw_rectangle(self, event):
        if self.start_x is None or self.start_y is None:
            self.start_x, self.start_y = event.x, event.y
        # Ajustar las coordenadas del rectángulo con la escala y los offsets
        scaled_start_x = (self.start_x - self.canvas_x_offset)/self.image_scale
        scaled_start_y = (self.start_y - self.canvas_y_offset)/self.image_scale
        scaled_end_x = (event.x - self.canvas_x_offset)/self.image_scale
        scaled_end_y = (event.y - self.canvas_y_offset)/self.image_scale
    #
    #
    #
    ##########################################################################################
    #*********       Funciones de los botones de Parámetros de referencia        ************#
    #***********************              2da Fila                    ***********************#
    #***********    Cálculo de distancias y validación de captura de datos      *************#
    ##########################################################################################
    #
    #
    #
    #******************************************************************************************#
    #*********  Funciones para la captura y validación de valores de referencia     ***********#
    #******************************************************************************************#
    #
    # Función para validar si el valor ingresado es numérico
    def validar_numero(self, value):
        if value == "" or value.replace(".", "", 1).isdigit():
            return True
        return False


    # Función para validar y actualizar las variables: Sincroniza las variables con los campos de entrada
    def validar_y_actualizar(self, *args):
        try:
            self.ValorPixel.set(float(self.pixels_entry.get()))
            self.ValorDistancia.set(float(self.distance_entry.get()))
            if hasattr(self, 'length_entry') and self.length_entry is not None:
                self.ValorLongitud.set(float(self.length_entry.get()))
        except ValueError:
            self.pixels_entry.delete(0, tk.END)
            self.pixels_entry.insert(0, "0.0")
            pass  # Ignorar si la entrada está vacía o no es válida

    # Función para validar y calcular la conversión de píxeles a distancia mediante la tecla Enter
    def validar_y_calcular(self, event=None):
        self.validar_y_actualizar()
        self.realizar_calculo()
        self.toggle_estado_boton("pixels")


    # Función para activar o desactivar los botones de píxeles y distancia
    def toggle_estado_boton(self, button_type):
        if button_type == "pixels":
            # Activar botón de Pixeles (solo se activa desde el campo Entry)
            self.pixels_button.config(relief=tk.SUNKEN, bg="lightgreen")
            self.button_states["pixels"] = True
            self.pixels_entry.config(state=tk.DISABLED)
            # Asegura que el botón de Referencia esté disponible
            self.distance_button.config(state=tk.NORMAL)
            self.distance_entry.config(state=tk.NORMAL)
        elif button_type == "distance":
            # Activar botón de Referencia (solo se activa después de haber activado el de Pixeles)
            self.distance_button.config(relief=tk.SUNKEN, bg="lightgreen")
            self.button_states["distance"] = True
            self.distance_entry.config(state=tk.DISABLED)
            # Asegura que el botón de Pixeles esté también bloqueado
            self.pixels_button.config(relief=tk.SUNKEN, bg="lightgreen")
            self.button_states["pixels"] = True
            self.pixels_entry.config(state=tk.DISABLED)


    # Realiza el cálculo de conversión usando los valores de píxeles y distancia
    def realizar_calculo(self):
        try:
            valor_pixel = self.ValorPixel.get()
            valor_distancia = self.ValorDistancia.get()
            if valor_pixel <= 0 or valor_distancia <= 0:
                return
            conversion = valor_distancia/valor_pixel
            self.ValorConversion = conversion
            self.conversion_label.config(text=f"{conversion:.2f}")
            # Solo calcular longitud si se ha trazado una línea o se ingresó manualmente
            if self.MedicionPixeles > 0:
                nueva_longitud = self.MedicionPixeles*conversion
                self.lengthLine_entry.delete(0, tk.END)
                self.lengthLine_entry.insert(0, f"{nueva_longitud:.2f}")
                self.ValorLongitud.set(nueva_longitud)
            # Escalar los límites
            nuevo_limite = 400*conversion
            self.min_radius_slider.config(state=tk.NORMAL, to=nuevo_limite)
            self.max_radius_slider.config(state=tk.NORMAL, to=nuevo_limite)
            self.min_dist_slider.config(state=tk.NORMAL, to=nuevo_limite)
            # Actualizar sliders con valores actuales
            self.update_min_radius(self.min_radius_slider.get())
            self.update_max_radius(self.max_radius_slider.get())
            self.update_min_dist(self.min_dist_slider.get())
            # Actualizar largo y ancho si son válidos
            largo = self.ValorLargo.get()
            ancho = self.ValorAncho.get()
            if largo > 0 and ancho > 0:
                nuevo_largo = largo*conversion
                nuevo_ancho = ancho*conversion
                self.ladoL_entry.delete(0, tk.END)
                self.ladoL_entry.insert(0, f"{nuevo_largo:.2f}")
                self.ladoA_entry.delete(0, tk.END)
                self.ladoA_entry.insert(0, f"{nuevo_ancho:.2f}")

        except Exception as e:
            messagebox.showerror("Error", f"Entrada inválida: {e}")
            default_slider_values = {'equalize_hist': 0, 'contrast': 0}
            self.sync_sliders(default_slider_values)


    # Función para resetear las mediciones y campos de entrada
    def reset_measurement(self):
        # Reiniciar variables
        self.start_x, self.start_y = None, None
        self.rect_id = None
        self.line_id = None
        self.MedicionPixeles = 0.0
        self.ValorLargo.set(0.0)
        self.ValorAncho.set(0.0)
        self.ValorConversion = 1.0
        self.ValorPixel.set(0.0)
        self.ValorDistancia.set(0.0)
        self.ValorLongitud.set(0.0)
        # Limpiar campos de entrada
        self.pixels_entry.delete(0, tk.END)
        self.pixels_entry.insert(0, "0.0")
        self.distance_entry.delete(0, tk.END)
        self.distance_entry.insert(0, "0.0")
        self.lengthLine_entry.delete(0, tk.END)
        self.lengthLine_entry.insert(0, "0.0")
#        self.ladoL_entry.delete(0, tk.END)
#        self.ladoL_entry.insert(0, "0.0")
#        self.ladoA_entry.delete(0, tk.END)
#        self.ladoA_entry.insert(0, "0.0")
        # Restablecer valor predeterminado del menú desplegable
        self.distance_units_var.set("px")
        # Actualizar etiquetas relacionadas con las unidades
        self.update_labels(self.distance_units_var.get())        
        radio_text = f"({self.distance_units_var.get()})"       # Texto para las unidades de distancia
        # Actualizar los límites del deslizador usando el valor de conversión
        nuevo_limite_maximo = 400                               # Escalar el límite superior
        self.max_radius_slider.config(to=nuevo_limite_maximo)   # Actualizar el límite superior
        nuevo_limite_minimo = 400                               # Escalar el límite superior
        self.min_radius_slider.config(to=nuevo_limite_minimo)   # Actualizar el límite superior
        nuevo_limite_dist = 400                                 # Escalar el límite superior
        self.min_dist_slider.config(to=nuevo_limite_dist)       # Actualizar el límite superior


    # # Función para actualizar las etiquetas de unidades de medida
    def update_labels(self, new_unit):
        self.lengthLine_unit_label.config(text=new_unit)            # Unidades para la línea
        self.unidadesConversion_label.config(text=f"{new_unit}/px") # Unidades de conversión
        self.distance_units_var.set("px")                           #
        self.conversion_label.config(text=f"1.0")                   # Actualizar la etiqueta de conversión 
    #
    #
    #
    ##########################################################################################
    #****************************************************************************************#
    ###################             Funciones de los botones            ######################
    ###################            procesamiento de imágenes            ######################
    #****************************************************************************************#
    ##########################################################################################
    #
    #
    ##########################################################################################
    #*********       Funciones de los botones de procesamiento de imágenes        ***********#
    #***********************              1ra Fila                    ***********************#
    #*********************************                       ********************************#
    ##########################################################################################
    #
    #
    # Función para procesar la imagen y actualizarla en el canvas
    def process_and_update_image(self, process_function, *args, **kwargs):
        if self.temp_image is None:
            messagebox.showinfo("Procesamiento de imagen", "No hay imagen para procesar.")
            return
        self.save_state()
        # Limpiar contornos anteriores
        for obj_id in self.contour_canvas_ids:
            self.canvas.delete(obj_id)
        self.contour_canvas_ids.clear()
        self.contour_original_coords.clear()
        # Limpiar mediciones
        self.canvas.delete("medicion")
        self.medicion_lineas.clear()
        self.medicion_rectangulos.clear()
        self.line_id = None
        self.rect_id = None
        # Limpiar anotaciones manuales (si aplica)
        for cid in getattr(self, "evaluation_canvas_ids", []):
            self.canvas.delete(cid)
        self.evaluation_canvas_ids.clear()
        self.manual_annotations.clear()
        self.patron_intensidad_referencia = None
        self.radio_referencia_manual = None
            
        img = self.temp_image
        if isinstance(img, Image.Image):
            img = np.array(img)
        if img.ndim == 3 and img.shape[-1] == 4:
            img = cv2.cvtColor(img, cv2.COLOR_RGBA2RGB)
        processed_img = process_function(img, *args, **kwargs)
        self.temp_image = Image.fromarray(processed_img)
        self.display_cv_image(processed_img)


    # Función para restablecer la imagen original y los deslizadores
    def reset_image(self):
        if self.original_image is None:
            return
        # Restaurar la imagen original
        self.save_state()
        self.temp_image = self.original_image.copy()
        self.scale_factor = 1.0
        self.update_zoom_display()
        # Restaurar deslizadores
        default_slider_values = {'equalize_hist': 0, 'contrast': 0}
        self.sync_sliders(default_slider_values)
        # Restaurar segmentación y color
        self.lower_bound = None
        self.upper_bound = None
        self.update_color_display("N/A", "N/A", "N/A")
        self.is_selecting_color = True
        # Limpiar contornos
        self.contour_original_coords.clear()
        for obj_id in self.contour_canvas_ids:
            self.canvas.delete(obj_id)
        self.contour_canvas_ids.clear()
        # Limpiar mediciones
        self.canvas.delete("medicion")
        self.medicion_lineas.clear()
        self.medicion_rectangulos.clear()
        self.line_id = None
        self.rect_id = None
        self.canvas.update_idletasks()
        # Restaurar botones de color
        self.color1_button.config(state=tk.DISABLED, relief=tk.SUNKEN)
        self.color2_button.config(state=tk.DISABLED, relief=tk.SUNKEN)
        # Restaurar elementos del menú de segmentación
        self.actualizar_metodo_segmentacion("Segmentar color")
        self.ocultar_botones_color()
        self.ocultar_campo_k()
        self.ocultar_instruccion_color()
        #
        self.patron_intensidad_referencia = None
        self.radio_referencia_manual = None
        self.btn_buscar.config(state=tk.DISABLED)




    # Función para sincronizar los deslizadores con los valores especificados
    def sync_sliders(self, values):
        # Sliders de histogramas y contraste
        self.slider_equalize_hist.set(values.get('equalize_hist', 0))
        self.slider_contrast.set(values.get('contrast', 0))


    # Función para equalizar el histograma de la imagen
    def update_equalize_hist(self, val):
        self.save_state()
        value = int(float(val))  # conversión robusta por si viene como string
        self.equalize_value_label.config(text=str(value))  # actualizar etiqueta visual
        # Convertir el valor del slider a un factor de mezcla
        alpha = value/100.0
        # Definir la función de equalización del histograma
        def equalize_hist(image, alpha):
            original_image = image.copy()
            if len(original_image.shape) == 2:  # Escala de grises
                equalized = cv2.equalizeHist(original_image)
                return cv2.addWeighted(original_image, 1 - alpha, equalized, alpha, 0)
            else:  # Color
                yuv = cv2.cvtColor(original_image, cv2.COLOR_BGR2YUV)
                yuv[:, :, 0] = cv2.equalizeHist(yuv[:, :, 0])
                equalized = cv2.cvtColor(yuv, cv2.COLOR_YUV2BGR)
                return cv2.addWeighted(original_image, 1 - alpha, equalized, alpha, 0)
        self.process_and_update_image(equalize_hist, alpha)


    # Función para ajustar el contraste de la imagen
    def update_contrast(self, val):
        # Guardar el estado actual antes de aplicar el contraste
        self.save_state()
        # Convertir el valor del slider a entero
        value = int(float(val))
        self.contrast_value_label.config(text=str(value))  # actualizar etiqueta visual
        # Calcular los parámetros de contraste
        alpha = 1 + (value/100.0)
        beta = 0
        # Definir la función de ajuste de contraste
        def adjust_contrast(image, alpha, beta):
            return cv2.convertScaleAbs(image, alpha=alpha, beta=beta)
        # Procesar la imagen con el ajuste de contraste
        self.process_and_update_image(adjust_contrast, alpha, beta)


    # Función para ajustar el radio mínimo de los círculos detectados
    def adjust_slider(self, slider, step, callback):
        current = slider.get()
        new_value = current + step
        # Limitar el valor dentro del rango del slider
        new_value = max(slider.cget("from"), min(slider.cget("to"), new_value))
        slider.set(new_value)
        callback(new_value)
    #
    #
    #*********************************************************************#
    #*********  Funciones para la segmentación de la imagen       ********#
    #*********************************************************************#
    #
    #
    def actualizar_metodo_segmentacion(self, metodo_nombre):
        self.segment_menu_button.config(text=f"{metodo_nombre} \u25BC")
    def iniciar_color_segmentacion(self):
        self.ocultar_campo_k()
        self.actualizar_metodo_segmentacion("Segmentar x color")
        self.start_segmentation()
    def iniciar_otsu_segmentacion(self):
        self.save_state()
        self.ocultar_botones_color()
        self.ocultar_campo_k()
        self.ocultar_instruccion_color()
        self.actualizar_metodo_segmentacion("Blanco y negro")
        self.apply_otsu_threshold()
    def iniciar_watershed_segmentacion(self):
        self.save_state()
        self.ocultar_botones_color()
        self.ocultar_campo_k()
        self.ocultar_instruccion_color()
        self.actualizar_metodo_segmentacion("Separar objetos")
        self.segmentar_watershed()
    def preparar_kmeans(self):
        self.save_state()
        self.actualizar_metodo_segmentacion("Colores similares")
        self.ocultar_botones_color()
        self.ocultar_instruccion_color()
        self.frame_k_entry.pack(side=tk.TOP, pady=(2, 2))
        self.k_hint_label.pack(side=tk.TOP)
        self.k_entry.config(state="normal")
        self.k_entry.focus_set()
    # Función para ocultar los botones de selección de color 1 y 2
    def ocultar_botones_color(self):
        self.color1_button.pack_forget()
        self.color2_button.pack_forget()
        self.color_buttons_frame.pack_forget()
    # Función para ocultar el campo de entrada K
    def ocultar_campo_k(self):
        self.k_entry.config(state="disabled")
        self.frame_k_entry.pack_forget()
        self.k_hint_label.pack_forget()
    # Función para ocultar la etiqueta de sugerencia de color
    def ocultar_instruccion_color(self):
        self.color_hint_label.pack_forget()
    # Asegura que la imagen esté en formato BGR (3 canales)
    def ensure_bgr_format(self, image):
        if len(image.shape) == 2 or image.shape[2] == 1:
            image = cv2.cvtColor(image, cv2.COLOR_GRAY2BGR)
        return image

    # Función par inciar el proceso de segmentación
    def start_segmentation(self):
        if self.temp_image is None:
            messagebox.showinfo("Segmentación", "No hay imagen cargada.")
            return
        # Mostrar y volver a empacar los botones de color
        self.color_buttons_frame.pack(side=tk.TOP, pady=(2, 2))
        self.color1_button.pack(side=tk.LEFT, padx=2)
        self.color2_button.pack(side=tk.LEFT, padx=2)
        self.color1_button.config(state=tk.NORMAL, relief=tk.RAISED)
        self.color2_button.config(state=tk.DISABLED, relief=tk.SUNKEN)
        # Mostrar la etiqueta de sugerencia
        self.color_hint_label.pack(side=tk.TOP)
        # Inicializar estado para la selección de color
        self.lower_bound = None
        self.upper_bound = None
        self.temp_color = None
        self.is_selecting_color = True
        self.current_selection = 'lower'
        # Activar evento de selección
        self.canvas.bind("<Button-1>", self.handle_color_selection)




    # Función para manejar la selección de color en la imagen
    def handle_color_selection(self, event):
        if not self.is_selecting_color or self.temp_image is None:
            return
        color_rgb = self.get_selected_color(event.x, event.y)
        if color_rgb is None:
            return
        # Convertir a HSV y almacenar temporalmente
        hsv_color = cv2.cvtColor(np.uint8([[color_rgb]]), cv2.COLOR_RGB2HSV)[0][0]
        self.temp_color = hsv_color
        # Actualizar la visualización
        self.update_color_display(color_rgb)

    # Función para confirmar la selección de color
    def confirm_color1(self):
        if self.temp_color is not None:
            self.lower_bound = np.clip(
                self.temp_color - np.array([10, 50, 50]),
                [0, 0, 0],
                [179, 255, 255]
            )
            # Activar selección del Color 2
            self.color1_button.config(state=tk.DISABLED, relief=tk.SUNKEN)
            self.color2_button.config(state=tk.NORMAL, relief=tk.RAISED)
            self.current_selection = 'upper'
            self.temp_color = None
            self.color_hint_label.config(text="Seleccione un color\ny presione el botón")

    # Función para confirmar la selección del Color 2 y aplicar la segmentación
    def confirm_color2(self):
        if self.temp_color is not None:
            self.upper_bound = np.clip(
                self.temp_color + np.array([10, 50, 50]),
                [0, 0, 0],
                [179, 255, 255]
            )
            # Guardar el estado actual
            self.save_state()
            # Finalizar proceso
            self.finish_color_selection()

    # Función para finalizar el proceso de selección de colores
    def finish_color_selection(self):
        if self.lower_bound is None or self.upper_bound is None:
            return
        self.is_selecting_color = False
        # Restaurar botones
        self.color1_button.config(state=tk.DISABLED, relief=tk.SUNKEN)
        self.color2_button.config(state=tk.DISABLED, relief=tk.SUNKEN)
        # Desactivar selección
        self.canvas.unbind("<Button-1>")
        # Aplicar segmentación
        self.apply_segmentation()
        # Limpiar estado
        self.lower_bound = None
        self.upper_bound = None
        self.temp_color = None
        # Ocultar los botones después de aplicar segmentación
        self.color1_button.pack_forget()
        self.color2_button.pack_forget()
        self.color_buttons_frame.pack_forget()
        # Actualizar la etiqueta de sugerencia
        self.color_hint_label.pack_forget()

    # Obtiene el color RGB del píxel seleccionado en las coordenadas (x, y)
    def get_selected_color(self, x=None, y=None):
        if self.temp_image is None:
            return None
        # Convertir PIL a NumPy si es necesario
        img_np = self.temp_image
        if isinstance(img_np, Image.Image):
            img_np = np.array(img_np)
        # Asegurarse de que la imagen esté en formato BGR
        if img_np.ndim == 3 and img_np.shape[-1] == 4:
            img_np = cv2.cvtColor(img_np, cv2.COLOR_RGBA2RGB)
        # Obtener dimensiones de la imagen
        image_height, image_width = img_np.shape[:2]
        # Si no se proporcionan coordenadas, usar el centro
        if x is None or y is None:
            x, y = image_width // 2, image_height // 2
        # Obtener dimensiones del canvas
        canvas_width = self.canvas.winfo_width()
        canvas_height = self.canvas.winfo_height()
        # Escala entre imagen y canvas
        scale_x = image_width/canvas_width
        scale_y = image_height/canvas_height
        # Coordenadas ajustadas
        img_x = int(x*scale_x)
        img_y = int(y*scale_y)
        # Verificar que las coordenadas estén dentro del rango de la imagen
        if 0 <= img_x < image_width and 0 <= img_y < image_height:
            color_bgr = img_np[img_y, img_x]
            color_rgb = color_bgr[::-1]
            return color_rgb
        else:
            messagebox.showinfo("Información", "Coordenadas fuera de rango.")
            return None

    # Aplica la segmentación usando los límites de color seleccionados.
    def apply_segmentation(self):
        def process(image):
            image = self.ensure_bgr_format(image)
            hsv_image = cv2.cvtColor(image, cv2.COLOR_BGR2HSV)
            mask = cv2.inRange(hsv_image, self.lower_bound, self.upper_bound)
            segmented_image = cv2.bitwise_and(image, image, mask=mask)
            return segmented_image
        # Verificar si hay parámetros de segmentación
        if self.temp_image is None or self.lower_bound is None or self.upper_bound is None:
            messagebox.showinfo("Información", "No hay parámetros para segmentar.")
            return
        self.process_and_update_image(process)


    # Actualiza la visualización del color seleccionado y el rango
    def update_color_display(self, color_rgb, lower_bound=None, upper_bound=None):
        if lower_bound is None or upper_bound is None:
            lower_bound, upper_bound = "N/A", "N/A"
    #
    #----------------------------------------------------------------------------------------#
    #
    # Función para aplicar binarización a la imagen con Otzu
    def apply_otsu_threshold(self):
        # Guardar el estado actual antes de procesar la imagen
        self.save_state()
        # Función interna para aplicar el umbral de Otsu
        def otsu_threshold(image):
            image = self.ensure_bgr_format(image)
            gray = cv2.cvtColor(image, cv2.COLOR_BGR2GRAY)
            _, thresh_image = cv2.threshold(gray, 0, 255, cv2.THRESH_BINARY + cv2.THRESH_OTSU)
            return thresh_image
        self.process_and_update_image(otsu_threshold)
    #
    #----------------------------------------------------------------------------------------#
    #    
    def segmentar_watershed(self):
        # Guardar el estado actual antes de procesar
        self.save_state()
        # Función interna para aplicar la segmentación por watershed
        def watershed_segmentation(image):
            if image is None:
                return image
            img = self.ensure_bgr_format(image.copy())
            # Convertir a escala de grises
            gray = cv2.cvtColor(img, cv2.COLOR_BGR2GRAY)
            # Binarizar con Otsu
            _, thresh = cv2.threshold(gray, 0, 255, cv2.THRESH_BINARY + cv2.THRESH_OTSU)
            # Apertura morfológica para eliminar ruido
            kernel = np.ones((3, 3), np.uint8)
            opening = cv2.morphologyEx(thresh, cv2.MORPH_OPEN, kernel, iterations=2)
            # Fondo seguro
            sure_bg = cv2.dilate(opening, kernel, iterations=3)
            # Primer plano seguro
            dist_transform = cv2.distanceTransform(opening, cv2.DIST_L2, 5)
            _, sure_fg = cv2.threshold(dist_transform, 0.5 * dist_transform.max(), 255, 0)
            sure_fg = np.uint8(sure_fg)
            # Región desconocida
            unknown = cv2.subtract(sure_bg, sure_fg)
            # Marcadores para Watershed
            _, markers = cv2.connectedComponents(sure_fg)
            markers = markers + 1
            markers[unknown == 255] = 0
            # Aplicar Watershed
            markers = cv2.watershed(img, markers)
            # Dibujar bordes (-1) en rojo
            img[markers == -1] = [0, 0, 255]
            return img
        # Aplicar la función de procesamiento y actualizar canvas
        self.process_and_update_image(watershed_segmentation)
    #
    #----------------------------------------------------------------------------------------#
    #
    # Función para manejar la entrada del usuario al presionar Enter en el campo K
    def on_enter_k(self, event):
        if self.temp_image is None:
            messagebox.showwarning("Imagen no cargada", "Primero debe cargar una imagen.")
            return        
        try:
            k = int(self.k_entry.get())
            if k < 2:
                raise ValueError
            self.segmentar_kmeans_con_k(k)
            self.ocultar_campo_k()  # Oculta al finalizar
        except ValueError:
            messagebox.showerror("Valor inválido", "Por favor, introduce un número entero mayor o igual a 2 para K.")


    # Función para segmentar la imagen usando K-means con el valor de K proporcionado
    def segmentar_kmeans_con_k(self, k):
        self.save_state()
        def kmeans_segmentation(image):
            if image is None:
                return image
            image = self.ensure_bgr_format(image)
            Z = image.reshape((-1, 3))
            Z = np.float32(Z)
            criterios = (cv2.TERM_CRITERIA_EPS + cv2.TERM_CRITERIA_MAX_ITER, 10, 1.0)
            _, etiquetas, centros = cv2.kmeans(Z, k, None, criterios, 10, cv2.KMEANS_RANDOM_CENTERS)
            centros = np.uint8(centros)
            segmentada = centros[etiquetas.flatten()].reshape(image.shape)
            return segmentada
        self.process_and_update_image(kmeans_segmentation)
    #
    #
    ##########################################################################################
    #*********       Funciones de los botones de procesamiento de imágenes        ***********#
    #***********************              2da Fila                    ***********************#
    #*********************************                       ********************************#
    ##########################################################################################
    #
    # Función para invertir los colores de la imagen
    def invert_colors(self):
        # Guardar el estado actual antes de procesar la imagen
        self.save_state()
        # Función interna para invertir los colores
        def invert(image):
            return cv2.bitwise_not(image)
        self.process_and_update_image(invert)


    # Función para convertir la imagen a escala de grises
    def convert_to_grayscale(self):
        # Guardar el estado actual antes de procesar la imagen
        self.save_state()
        # Función interna para convertir a escala de grises
        def to_grayscale(image):
            if len(image.shape) == 3:
                return cv2.cvtColor(image, cv2.COLOR_BGR2GRAY)
            return image
        self.process_and_update_image(to_grayscale)
    #
    #
    #
    ##########################################################################################
    #*********       Funciones de los botones de parAmetros de contornos          ***********#
    #***********************              3ra Fila                    ***********************#
    #*********************************                       ********************************#
    ##########################################################################################
    #
    #
    # Función para limpiar los contornos dibujados en la imagen
    def clear_contours(self):
        if self.temp_image is None:
            return
        self.save_state()
        # Eliminar contornos
        if hasattr(self, 'contour_canvas_ids'):
            for obj_id in self.contour_canvas_ids:
                self.canvas.delete(obj_id)
            self.contour_canvas_ids.clear()
        self.contour_original_coords.clear()
        # Eliminar las mediciones (líneas/rectángulos)
        self.canvas.delete("medicion")
        self.medicion_lineas.clear()
        self.medicion_rectangulos.clear()
        # Redibujar imagen
        img_clean = self.temp_image.copy()
        new_width = int(img_clean.width*self.scale_factor)
        new_height = int(img_clean.height*self.scale_factor)
        img_resized = img_clean.resize((new_width, new_height), Image.Resampling.LANCZOS)
        self.img_tk = ImageTk.PhotoImage(img_resized)
        self.x_offset, self.y_offset = self.calculate_centered_coordinates(new_width, new_height)
        self.canvas.create_image(self.x_offset, self.y_offset, anchor="nw", image=self.img_tk, tags="image")
        self.canvas.image = self.img_tk
        self.canvas.config(scrollregion=(0, 0, new_width, new_height))
        # Forzar refresco visual
        self.canvas.update_idletasks()


    # Funciones para actualizar los parámetros de la detección de círculos
    def update_param1(self, val):
        valor = int(float(val))
        self.param1 = valor
        self.param1_value_label.config(text=str(valor))
    def update_param2(self, val):
        valor = int(float(val))
        self.param2 = valor
        self.param2_value_label.config(text=str(valor))
    def update_min_dist(self, val):
        valor = float(val)
        self.min_dist = valor
        self.min_dist_value_label.config(text=f"{valor:.0f}")
    def update_min_radius(self, val):
        valor = float(val) 
        self.min_radius = valor
        self.min_radius_value_label.config(text=f"{valor:.0f}")
    def update_max_radius(self, val):
        valor = float(val)
        self.max_radius = valor
        self.max_radius_value_label.config(text=f"{valor:.0f}")


    # Función para restablecer los valores de los deslizadores y la imagen
    def reset_sliders_and_image(self):
        if self.ValorConversion <= 0:
            self.ValorConversion = 1.0  # valor de respaldo para evitar errores
        # --- Valores base en unidades por defoult ---
        default_min_dist = 20.0
        default_min_radius = 10.0
        default_max_radius = 50.0
        default_param1 = 50
        default_param2 = 30
        # --- Convertir a píxeles ---
        min_dist_px = int(default_min_dist/self.ValorConversion)
        min_radius_px = int(default_min_radius/self.ValorConversion)
        max_radius_px = int(default_max_radius/self.ValorConversion)
        # --- Establecer límites dinámicos (en píxeles) ---
        max_slider_px = int(400/self.ValorConversion)
        self.min_dist_slider.config(from_=1, to=max_slider_px)
        self.min_radius_slider.config(from_=1, to=max_slider_px)
        self.max_radius_slider.config(from_=1, to=max_slider_px)
        # --- Establecer valores predeterminados ---
        self.min_dist_slider.set(min_dist_px)
        self.param1_slider.set(default_param1)
        self.param2_slider.set(default_param2)
        self.min_radius_slider.set(min_radius_px)
        self.max_radius_slider.set(max_radius_px)
        # --- Forzar actualización visual y lógica ---
        self.update_min_dist(min_dist_px)
        self.update_param1(default_param1)
        self.update_param2(default_param2)
        self.update_min_radius(min_radius_px)
        self.update_max_radius(max_radius_px)

#    def sync_entry_with_sliders(self):
#        self.min_dist_entry.delete(tk.END)
#        self.min_dist_entry.insert(self.min_dist_slider.get())
#        self.param1_entry.delete(0, tk.END)
#        self.param1_entry.insert(0, str(self.param1_slider.get()))
#        self.param2_entry.delete(0, tk.END)
#        self.param2_entry.insert(0, str(self.param2_slider.get()))
#        self.min_radius_entry.delete(0, tk.END)
#        self.min_radius_entry.insert(0, str(self.min_radius_slider.get()))
#        self.max_radius_entry.delete(0, tk.END)
#        self.max_radius_entry.insert(0, str(self.max_radius_slider.get()))



    # Función para actualizar los parámetros con los valores ajustados por el usuario
    def update_parameters(self, min_dist, param1, param2, min_radius, max_radius):
        self.min_dist = min_dist        #
        self.param1 = param1            #
        self.param2 = param2            #
        self.min_radius = min_radius    #
        self.max_radius = max_radius    #


    # Función para aplicar los parámetros seleccionados ----#
    def on_apply_parameters_button_click(self):             #
        try:                                                #
            min_dist = float(self.min_dist_entry.get())     # Distancia mínima entre los centros de los círculos
            param1 = float(self.param1_entry.get())         # Umbral para el detector de bordes
            param2 = float(self.param2_entry.get())         # Umbral para la detección de círculos
            min_radius = float(self.min_radius_entry.get()) # Radio mínimo
            max_radius = float(self.max_radius_entry.get()) # Radio máximo     
        except ValueError:
            messagebox.showwarning("Advertencia", "Ingrese valores válidos en todas las entradas.")
            return
        self.selected_shape.set("Círculos")     # Forzar selección de contornos circulares
        self.apply_parameters(min_dist, param1, param2, min_radius, max_radius) # Aplicar parámetros

    # Función para aplicar parámetros seleccionados según la forma elegida
    def apply_parameters(self, min_dist, param1, param2, min_radius, max_radius):
        self.update_parameters(min_dist, param1, param2, min_radius, max_radius)
        if self.selected_shape.get() == "Círculos":             # Verificar si se seleccionaron círculos
            self.update_image_for_circles(min_dist, param1, param2, min_radius, max_radius)
        elif self.selected_shape.get() == "Otros":              # Verificar si se seleccionaron contornos amorfos     
            self.update_image_for_amorphous(min_dist, param1, param2, min_radius, max_radius)
        else:
            messagebox.showwarning("Advertencia", "Selección inválida para los parámetros.")
            return


    # Función para contar los contornos circulares -----------------#
    def update_image_for_circles(self, min_dist, param1, param2, min_radius, max_radius):
        # Convertir diámetros a radios (los sliders muestran diámetro, pero HoughCircles usa radios)
        min_radius = min_radius/2
        max_radius = max_radius/2
        if self.temp_image is None:
            messagebox.showwarning("Advertencia", "No hay imagen cargada para aplicar los parámetros.")
            return []
        # Validar factor de conversión
        if self.ValorConversion <= 0:
            messagebox.showwarning("Advertencia", "El factor de conversión es inválido.")
            return []
        # Convertir imagen temporal a formato NumPy
        img_np = np.array(self.temp_image)
        img_with_circles = img_np.copy()
        if len(img_with_circles.shape) == 2 or img_with_circles.shape[2] == 1:
            img_with_circles = cv2.cvtColor(img_with_circles, cv2.COLOR_GRAY2BGR)
        # Limpiar canvas y coordenadas
        for obj_id in self.contour_canvas_ids:
            self.canvas.delete(obj_id)
        self.contour_canvas_ids.clear()
        self.contour_original_coords.clear()
        # Preprocesamiento
        img_gray = cv2.cvtColor(img_np, cv2.COLOR_RGB2GRAY) if img_np.ndim == 3 else img_np
        img_gray = cv2.bilateralFilter(img_gray, 9, 75, 75)
        clahe = cv2.createCLAHE(clipLimit=2.0, tileGridSize=(8, 8))
        img_gray = clahe.apply(img_gray)
        # Parámetros de HoughCircles
        minRadius_pixels = int(min_radius/self.ValorConversion)
        maxRadius_pixels = int(max_radius/self.ValorConversion)
        minDist_pixels = min_dist/self.ValorConversion
        # Detectar círculos usando HoughCircles
        circles = cv2.HoughCircles(
            img_gray, cv2.HOUGH_GRADIENT, dp=1, minDist=minDist_pixels,
            param1=param1, param2=param2,
            minRadius=minRadius_pixels, maxRadius=maxRadius_pixels
        )
        # Inicializar lista para almacenar diámetros de círculos
        num_circles = []
        if circles is not None:
            circles = np.uint16(np.around(circles))
            for i in circles[0, :]:
                radius_pixels = i[2]
                if minRadius_pixels <= radius_pixels <= maxRadius_pixels:
                    center = (i[0], i[1])
                    diameter_converted = radius_pixels
                    num_circles.append(diameter_converted)
                    # Coordenadas originales del círculo
                    circle_contour = [
                        (center[0] + radius_pixels*np.cos(t), center[1] + radius_pixels*np.sin(t))
                        for t in np.linspace(0, 2*np.pi, 20)
                    ]
                    original_circle_contour = [(x, y) for x, y in circle_contour]  # guardar sin escalar
                    self.contour_original_coords.append((original_circle_contour, "red"))
                    # Dibujar en canvas
                    scaled = [(x*self.scale_factor + self.x_offset, y*self.scale_factor + self.y_offset)
                              for x, y in circle_contour]
                    flat = [coord for point in scaled for coord in point]
                    cid = self.canvas.create_line(flat, fill="red", width=2, smooth=True)
                    self.contour_canvas_ids.append(cid)
                    # Dibujar en la imagen
                    cv2.circle(img_with_circles, center, radius_pixels, (255, 0, 0), 2)
                    cv2.circle(img_with_circles, center, 2, (0, 0, 255), 3)
        # Actualizar imagen procesada
        self.processed_image = cv2.cvtColor(img_with_circles, cv2.COLOR_BGR2RGB)
        self.display_cv_image(self.processed_image)
        return num_circles


    # Función para contar los contornos amorfos ---------------#
    def update_image_for_amorphous(self, min_dist, param1, param2, min_radius, max_radius):
        if self.temp_image is None:
            messagebox.showwarning("Advertencia", "No hay imagen cargada para aplicar los parámetros.")
            return []
        #
        img_with_contours = np.array(self.temp_image).copy()
        if len(img_with_contours.shape) == 2 or img_with_contours.shape[2] == 1:
            img_with_contours = cv2.cvtColor(img_with_contours, cv2.COLOR_GRAY2BGR)
        # Validar factor de conversión
        conversion = self.ValorConversion
        if conversion <= 0:
            messagebox.showwarning("Advertencia", "El factor de conversión es inválido.")
            return []
        # Limpiar canvas y coordenadas
        for obj_id in self.contour_canvas_ids:
            self.canvas.delete(obj_id)
        self.contour_canvas_ids.clear()
        self.contour_original_coords.clear()
        # Preprocesamiento de la imagen
        img_gray = cv2.cvtColor(img_with_contours, cv2.COLOR_RGB2GRAY) if img_with_contours.ndim == 3 else img_with_contours
        img_gray = cv2.bilateralFilter(img_gray, 9, 75, 75)
        clahe = cv2.createCLAHE(clipLimit=2.0, tileGridSize=(8, 8))
        img_gray = clahe.apply(img_gray)
        edges = cv2.Canny(img_gray, param1, param2)
        contours, _ = cv2.findContours(edges, cv2.RETR_EXTERNAL, cv2.CHAIN_APPROX_SIMPLE)
        # Filtrar contornos por tamaño
        filtered_contours = [
            cnt for cnt in contours if min_radius/conversion <= cv2.arcLength(cnt, True) <= max_radius/conversion
        ]
        # Inicializar lista para almacenar diámetros de contornos
        for cnt in filtered_contours:
            points = [(int(p[0]), int(p[1])) for p in cnt.reshape(-1, 2)]
            self.contour_original_coords.append((points, "blue"))
            # Dibujar contornos en el canvas
            scaled = [(x*self.scale_factor + self.x_offset, y*self.scale_factor + self.y_offset) for x, y in points]
            flat = [coord for pt in scaled for coord in pt]
            cid = self.canvas.create_line(flat, fill="blue", width=2, smooth=True)
            self.contour_canvas_ids.append(cid)
        #
        # Dibujar los contornos sobre la imagen que se mostrará
        cv2.drawContours(img_with_contours, filtered_contours, -1, (255, 0, 0), 2)
        self.processed_image = cv2.cvtColor(img_with_contours, cv2.COLOR_BGR2RGB)
        self.display_cv_image(self.processed_image)
        # Calcular contornos aproximados
        num_circles = [math.sqrt(cv2.contourArea(cnt)/math.pi) for cnt in filtered_contours]
        return num_circles


    # Función para contar y actualizar la tabla
    def count_contours(self):
        # Verificar si hay una imagen original cargada
        if self.original_image is None:
            messagebox.showwarning("Advertencia", "No hay imagen cargada para contar contornos.")
            return
        try:
            min_dist = self.min_dist        # Distancia mínima entre los centros de los círculos 
            param1 = self.param1            # Umbral para el detector de bordes
            param2 = self.param2            # Umbral para la detección de círculos
            min_radius = self.min_radius    # Radio mínimo
            max_radius = self.max_radius    # Radio máximo
        except AttributeError as e:         # Manejo de errores
            messagebox.showwarning("Advertencia", "Ajustar los parámetros antes de contar los contornos.")
            return
        # Verificar la forma seleccionada y contar los contornos ---#
        if self.selected_shape.get() == "Círculos":                 # Seleccionar círculos
            num_circles = self.update_image_for_circles(min_dist, param1, param2, min_radius, max_radius)
        elif self.selected_shape.get() == "Otros":                  # Seleccionar contornos amorfos
            num_circles = self.update_image_for_amorphous(min_dist, param1, param2, min_radius, max_radius)
        else:
            messagebox.showwarning("Advertencia", "Por favor, seleccione una forma válida para contar los contornos.")
            return
        # Actualizar la tabla con los resultados
        if num_circles:
            self.add_results_to_table(num_circles)
        else:
            messagebox.showwarning("Advertencia", "No se detectaron contornos en la imagen.")


    # Función para redibujar los contornos en el canvas
    def redraw_contours(self):
        # Verificar si hay contornos para redibujar
        for cid in self.contour_canvas_ids:
            self.canvas.delete(cid)
        self.contour_canvas_ids.clear()
        # Redibujar los contornos originales
        for contour, color in self.contour_original_coords:
            # Escalar y desplazar al redibujar
            scaled = [(x*self.scale_factor + self.x_offset, y*self.scale_factor + self.y_offset)
                      for x, y in contour]
            flat = [coord for pt in scaled for coord in pt]
            cid = self.canvas.create_line(flat, fill=color, width=2, smooth=True)
            self.contour_canvas_ids.append(cid)


    # Función para agregar los resultados a la tabla
    def add_results_to_table(self, num_circles):
        medicion_num = len(self.results_table.get_children()) + 1   # Número de medición
        for idx, radio in enumerate(num_circles, start=1):          # Iterar sobre los diámetros
            diametro = 2*radio*self.ValorConversion                 # Diámetro en unidades físicas    
            unique_id = f"row_{medicion_num + idx - 1}"             # ID único para la fila
            self.results_table.insert("", "end", iid=unique_id, values=(medicion_num + idx - 1, f"{diametro:.2f}"))
        self.results_table.update_idletasks()                       # Actualizar la tabla
    #                                                               #
    #                                                               #
    ##########################################################################################
    ##########################################################################################
    #****************************************************************************************#
    ##################             Funciones para detección              #####################
    ###################             automática de contornos             ######################
    #****************************************************************************************#
    ##########################################################################################
    ##########################################################################################
    #                                                               #
    #                                                               #
    def estimar_parametros_por_referencia(self, tolerancia_porcentual=0.10):
        if self.ValorLongitud.get() <= 0:
            messagebox.showwarning("Advertencia", "Debe trazar una línea de referencia para medir el diámetro.")
            return None
        # Calcular el radio de referencia y la tolerancia
        radio_referencia = self.ValorLongitud.get() / 2
        tolerancia = radio_referencia * tolerancia_porcentual
        min_radius = radio_referencia - tolerancia
        max_radius = radio_referencia + tolerancia
        # Estimar distancia mínima entre centros basada en el radio máximo
        min_dist = max_radius
        # Valores por defecto para Canny
        param1 = 50
        param2 = 30
        return {
            "min_radius": min_radius,
            "max_radius": max_radius,
            "min_dist": min_dist,
            "param1": param1,
            "param2": param2
        }

    # Función para detectar círculos por referencia de forma automática
    def detectar_circulos_por_referencia(self):
        if self.temp_image is None:
            messagebox.showwarning("Advertencia", "No hay imagen cargada.")
            return
        # Asegurar selección de círculos
        self.selected_shape.set("Círculos")
        # Obtener parámetros estimados desde función reutilizable
        params = self.estimar_parametros_por_referencia(tolerancia_porcentual=0.10)
        if params is None:
            return
        # Extraer valores
        min_radius = params["min_radius"]
        max_radius = params["max_radius"]
        min_dist = params["min_dist"]
        param1 = params["param1"]
        param2 = params["param2"]
        # Actualizar sliders y valores internos
        self.min_radius_slider.set(min_radius * 2)
        self.max_radius_slider.set(max_radius * 2)
        self.min_dist_slider.set(min_dist)
        self.param1_slider.set(param1)
        self.param2_slider.set(param2)
        # Actualizar los valores internos
        self.update_min_radius(min_radius * 2)
        self.update_max_radius(max_radius * 2)
        self.update_min_dist(min_dist)
        self.update_param1(param1)
        self.update_param2(param2)
        # Aplicar parámetros y detectar contornos
        self.apply_parameters(min_dist, param1, param2, min_radius * 2, max_radius * 2)
        self.count_contours()

    #                                                               #
    #                                                               #
    ##########################################################################################
    ##########################################################################################
    #****************************************************************************************#
    ##################             Funciones para contornos              #####################
    ###################               selección de formas               ######################
    #****************************************************************************************#
    ##########################################################################################
    ##########################################################################################
    #                                                               #
    #                                                               #
    def evaluar_deteccion(self):
        if not self.contour_original_coords or not self.manual_annotations:
            messagebox.showinfo("Evaluación", "Debe haber detección automática y anotaciones manuales.")
            return
        for obj_id in self.evaluation_canvas_ids:
            self.canvas.delete(obj_id)
        self.evaluation_canvas_ids.clear()
        # Centroides de contornos detectados
        auto_coords = []
        for pts, _ in self.contour_original_coords:
            xs = [x for x, y in pts]
            ys = [y for x, y in pts]
            cx, cy = np.mean(xs), np.mean(ys)
            auto_coords.append((cx, cy))
        tp = 0
        matched_auto = set()
        matched_manual = set()
        for i, (xm, ym, _) in enumerate(self.manual_annotations):
            matched = False
            for j, (xa, ya) in enumerate(auto_coords):
                dist = np.sqrt((xm - xa)**2 + (ym - ya)**2)
                if dist <= self.match_threshold and j not in matched_auto:
                    matched = True
                    tp += 1
                    matched_auto.add(j)
                    matched_manual.add(i)
                    # TP -> verde
                    x, y = xa*self.scale_factor + self.x_offset, ya*self.scale_factor + self.y_offset
                    cid = self.canvas.create_oval(x-5, y-5, x+5, y+5, fill="green", outline="")
                    self.evaluation_canvas_ids.append(cid)
                    break
            if not matched:
                # FN -> azul
                x, y = xm*self.scale_factor + self.x_offset, ym*self.scale_factor + self.y_offset
                cid = self.canvas.create_oval(x-5, y-5, x+5, y+5, fill="blue", outline="")
                self.evaluation_canvas_ids.append(cid)
        for j, (xa, ya) in enumerate(auto_coords):
            if j not in matched_auto:
                # FP -> rojo
                x, y = xa*self.scale_factor + self.x_offset, ya*self.scale_factor + self.y_offset
                cid = self.canvas.create_oval(x-5, y-5, x+5, y+5, fill="red", outline="")
                self.evaluation_canvas_ids.append(cid)
        fn = len(self.manual_annotations) - tp
        fp = len(auto_coords) - tp
        precision = tp / (tp + fp) if tp + fp > 0 else 0
        recall = tp / (tp + fn) if tp + fn > 0 else 0
        f1 = 2 * precision * recall / (precision + recall) if (precision + recall) > 0 else 0
        messagebox.showinfo("Resultados",
                            f"TP: {tp}\nFP: {fp}\nFN: {fn}\n\nPrecisión: {precision:.2f}\nRecall: {recall:.2f}\nF1-score: {f1:.2f}")
    #                                                               #
    #                                                               #
    ##########################################################################################
    ##########################################################################################
    #****************************************************************************************#
    ##################             Funciones para detección              #####################
    ###################            de contornos automático              ######################
    #****************************************************************************************#
    ##########################################################################################
    ##########################################################################################
    #                                                               #
    #                                                               #
    def get_valid_conversion(self):
        if not hasattr(self, "ValorConversion") or self.ValorConversion <= 0:
            self.ValorConversion = 1.0
        return self.ValorConversion


    def buscar_candidatos_similares_automaticamente(self):
        if self.temp_image is None:
            messagebox.showwarning("Advertencia", "No hay imagen cargada.")
            return
        self.save_state()
        img_np = np.array(self.temp_image)
        img_gray = cv2.cvtColor(img_np, cv2.COLOR_RGB2GRAY) if img_np.ndim == 3 else img_np.copy()
        # Obtener el factor de conversión válido
        conversion = self.get_valid_conversion()
        # Leer parámetros desde patrón o sliders
        if hasattr(self, "radio_referencia_manual") and self.radio_referencia_manual is not None:
            radio_mm = self.radio_referencia_manual
            min_radius_um = radio_mm * 0.8
            max_radius_um = radio_mm * 1.2
            min_dist_um = radio_mm * 2
        else:
            # Usar valores del usuario directamente
            min_dist_um = self.min_dist_slider.get()
            min_radius_um = self.min_radius_slider.get() / 2
            max_radius_um = self.max_radius_slider.get() / 2
        # Convertir a píxeles
        min_dist_px = int(min_dist_um / conversion)
        min_radius_px = int(min_radius_um / conversion)
        max_radius_px = int(max_radius_um / conversion)
        # Condiciones iniciales
        mejor_num = 0
        mejor_param1 = 50
        mejor_param2 = 30
        mejor_circulos = []
        # Solo se escanean param1 y param2
        for param1 in range(30, 120, 10):
            for param2 in range(10, 60, 5):
                circles = cv2.HoughCircles(
                    img_gray,
                    cv2.HOUGH_GRADIENT,
                    dp=1,
                    minDist=min_dist_px,
                    param1=param1,
                    param2=param2,
                    minRadius=min_radius_px,
                    maxRadius=max_radius_px
                )
                if circles is not None and len(circles[0]) > mejor_num:
                    mejor_num = len(circles[0])
                    mejor_param1 = param1
                    mejor_param2 = param2
                    mejor_circulos = circles
        if mejor_num == 0:
            messagebox.showinfo("Resultado", "No se encontraron contornos similares automáticamente.")
            return
        # Dibujar los círculos encontrados
        img_color = cv2.cvtColor(img_gray, cv2.COLOR_GRAY2BGR)
        for i in mejor_circulos[0, :]:
            center = (int(round(i[0])), int(round(i[1])))
            radius = int(round(i[2]))
            radio_fisico = radius * conversion
            self.add_results_to_table([radio_fisico])
            puntos = [
                (center[0] + radius * np.cos(t), center[1] + radius * np.sin(t))
                for t in np.linspace(0, 2 * np.pi, 20)
            ]
            self.contour_original_coords.append((puntos, "orange"))
            scaled = [(x * self.scale_factor + self.x_offset, y * self.scale_factor + self.y_offset) for x, y in puntos]
            plano = [c for p in scaled for c in p]
            cid = self.canvas.create_line(plano, fill="orange", width=2, smooth=True)
            self.contour_canvas_ids.append(cid)
            cv2.circle(img_color, center, radius, (0, 165, 255), 2)
        self.processed_image = cv2.cvtColor(img_color, cv2.COLOR_BGR2RGB)
        self.display_cv_image(self.processed_image)
        # Actualizar sliders solo para intensidad de bordes
        self.param1_slider.set(mejor_param1)
        self.param2_slider.set(mejor_param2)
        self.update_param1(mejor_param1)
        self.update_param2(mejor_param2)
#        self.sync_entry_with_sliders()
        messagebox.showinfo("Resultado", f"Se encontraron {mejor_num} contornos similares automáticamente.")
    #                                                               #
    #                                                               #
    ##########################################################################################
    ##########################################################################################
    #****************************************************************************************#
    ##################             Funciones para detección              #####################
    ###################     de contornos mediante un patrón ejemplo     ######################
    #****************************************************************************************#
    ##########################################################################################
    ##########################################################################################
    #                                                               #
    #                                                               #
    def estimar_parametros_por_patron(self, tolerancia_porcentual=0.1):
        if not hasattr(self, "radio_referencia_manual") or self.radio_referencia_manual is None:
            messagebox.showwarning("Referencia no definida", "Debe seleccionar primero un patrón de contorno.")
            return None
        # Validar factor de conversión
        if not hasattr(self, "ValorConversion") or self.ValorConversion <= 0:
            self.ValorConversion = 1.0
        #
        r = self.radio_referencia_manual  # en unidades físicas
        diametro = r * 2
        tol = diametro * tolerancia_porcentual
        min_radius = (diametro - tol) / 2
        max_radius = (diametro + tol) / 2
        min_dist = 0.75 * diametro
        #
        param1 = 50  # Borde externo Canny
        param2 = 30  # Umbral acumulador Hough
        #
        return {
            "min_radius": min_radius,
            "max_radius": max_radius,
            "min_dist": min_dist,
            "param1": param1,
            "param2": param2
        }

    def restaurar_estado_marcado_fallido(self):
        # Desactivar eventos del canvas
        self.canvas.unbind("<Button-1>")
        self.canvas.unbind("<B1-Motion>")
        self.canvas.unbind("<ButtonRelease-1>")
        # Eliminar el círculo temporal si existe
        if hasattr(self, "temp_circle_id") and self.temp_circle_id is not None:
            self.canvas.delete(self.temp_circle_id)
            self.temp_circle_id = None
        # Restaurar botón "Seleccionar"
        self.btn_marcar.config(relief=tk.RAISED, state=tk.NORMAL, bg="lightgray")
        # Desactivar botón "Buscar"
        self.btn_buscar.config(state=tk.DISABLED)



    def detectar_por_patrón_manual(self):
        # Restaurar botón y desactivar modo marcado en caso de error
        self.btn_marcar.config(relief=tk.RAISED, state=tk.NORMAL, bg="lightgray")
        self.btn_buscar.config(state=tk.DISABLED)
        self.canvas.unbind("<Button-1>")
        self.canvas.unbind("<B1-Motion>")
        self.canvas.unbind("<ButtonRelease-1>")
        self.temp_circle_id = None
        if self.temp_image is None:
            messagebox.showwarning("Advertencia", "No hay imagen cargada.")
            self.restaurar_estado_marcado_fallido()
            return
        if not hasattr(self, "patron_intensidad_referencia") or self.patron_intensidad_referencia is None:
            messagebox.showwarning("Advertencia", "Primero marque un contorno manual como referencia.")
            self.restaurar_estado_marcado_fallido()
            return
        plantilla = self.patron_intensidad_referencia.copy().astype(np.uint8)
        if plantilla.shape[0] < 5 or plantilla.shape[1] < 5:
            messagebox.showwarning("Advertencia", "La plantilla es demasiado pequeña para la detección.")
            self.restaurar_estado_marcado_fallido()
            return
        img = np.array(self.temp_image)
        img_gray = cv2.cvtColor(img, cv2.COLOR_RGB2GRAY) if img.ndim == 3 else img.copy()
        ih, iw = img_gray.shape[:2]
        ph, pw = plantilla.shape[:2]
        if ih < ph or iw < pw:
            messagebox.showerror("Error", "La imagen es más pequeña que la plantilla.")
            self.restaurar_estado_marcado_fallido()
            return
        try:
            resultado = cv2.matchTemplate(img_gray, plantilla, cv2.TM_CCOEFF_NORMED)
        except cv2.error as e:
            messagebox.showerror("Error", f"Fallo en matchTemplate:\n{str(e)}")
            self.restaurar_estado_marcado_fallido()
            return
        # Procesamiento exitoso
        umbral = 0.8
        ubicaciones = list(zip(*np.where(resultado >= umbral)))
        r_px = plantilla.shape[0] // 2
        img_color = cv2.cvtColor(img_gray, cv2.COLOR_GRAY2BGR)
        for obj_id in self.contour_canvas_ids:
            self.canvas.delete(obj_id)
        self.contour_canvas_ids.clear()
        self.contour_original_coords.clear()
        centros_aceptados = []
        num_detectados = 0
        for (y, x) in ubicaciones:
            centro_actual = (x + r_px, y + r_px)
            if any(np.hypot(cx - centro_actual[0], cy - centro_actual[1]) < 2 * r_px for cx, cy in centros_aceptados):
                continue
            centros_aceptados.append(centro_actual)
            radio_fisico = r_px * self.ValorConversion
            self.add_results_to_table([radio_fisico])
            puntos = [
                (centro_actual[0] + r_px * np.cos(t), centro_actual[1] + r_px * np.sin(t))
                for t in np.linspace(0, 2 * np.pi, 20)
            ]
            self.contour_original_coords.append((puntos, "green"))
            scaled = [(x * self.scale_factor + self.x_offset, y * self.scale_factor + self.y_offset) for x, y in puntos]
            plano = [c for p in scaled for c in p]
            cid = self.canvas.create_line(plano, fill="green", width=2, smooth=True)
            self.contour_canvas_ids.append(cid)
            cv2.circle(img_color, centro_actual, r_px, (0, 255, 0), 2)
            num_detectados += 1
        self.processed_image = cv2.cvtColor(img_color, cv2.COLOR_BGR2RGB)
        self.display_cv_image(self.processed_image)
        if num_detectados == 0:
            messagebox.showinfo("Resultado", "No se encontraron coincidencias.")
        else:
            messagebox.showinfo("Resultado", f"Se encontraron {num_detectados} objetos similares.")
        self.btn_buscar.config(state=tk.DISABLED)



    def iniciar_marcado_manual(self):
        if self.temp_image is None:
            messagebox.showwarning("Imagen no cargada", "Primero debe cargar una imagen.")
            return
        # Visual: dejar botón "hundido"
        self.btn_marcar.config(relief=tk.SUNKEN, state=tk.DISABLED, bg="lightgreen")
        # Activar eventos del canvas
        self.canvas.bind("<Button-1>", self.marcar_centro)
        self.canvas.bind("<B1-Motion>", self.ajustar_radio)
        self.canvas.bind("<ButtonRelease-1>", self.finalizar_marcado)
        # Inicializar variables
        self.start_x, self.start_y = None, None
        self.temp_circle_id = None


    def marcar_centro(self, event):
        self.start_x, self.start_y = self.get_original_coordinates(event.x, event.y)
        x, y = self.start_x * self.scale_factor + self.x_offset, self.start_y * self.scale_factor + self.y_offset
        self.temp_circle_id = self.canvas.create_oval(x, y, x, y, outline="green", width=2)
    def ajustar_radio(self, event):
        if self.temp_circle_id is None:
            return
        end_x, end_y = self.get_original_coordinates(event.x, event.y)
        r = ((end_x - self.start_x)**2 + (end_y - self.start_y)**2)**0.5
        x0 = (self.start_x - r)*self.scale_factor + self.x_offset
        y0 = (self.start_y - r)*self.scale_factor + self.y_offset
        x1 = (self.start_x + r)*self.scale_factor + self.x_offset
        y1 = (self.start_y + r)*self.scale_factor + self.y_offset
        self.canvas.coords(self.temp_circle_id, x0, y0, x1, y1)


    def finalizar_marcado(self, event):
        if self.start_x is None or self.start_y is None:
            return
        end_x, end_y = self.get_original_coordinates(event.x, event.y)
        r = ((end_x - self.start_x)**2 + (end_y - self.start_y)**2)**0.5
        self.manual_annotations.append((self.start_x, self.start_y, r))
        self.evaluation_canvas_ids.append(self.temp_circle_id)
        self.temp_circle_id = None
        #
        cx, cy = self.start_x, self.start_y
        r = ((end_x - self.start_x)**2 + (end_y - self.start_y)**2)**0.5
        img = np.array(self.temp_image)
        if img.ndim == 3:
            img = cv2.cvtColor(img, cv2.COLOR_RGB2GRAY)
        #
        cx_px = int(cx)
        cy_px = int(cy)
        r_px = int(r)
        h, w = img.shape[:2]
        if r_px <= 1 or cx_px - r_px < 0 or cy_px - r_px < 0 or cx_px + r_px > w or cy_px + r_px > h:
            messagebox.showwarning("Advertencia", "El contorno está demasiado cerca del borde o es demasiado pequeño.")
            return
        #
        mask = np.zeros_like(img, dtype=np.uint8)
        cv2.circle(mask, (cx_px, cy_px), r_px, 255, -1)
        roi = cv2.bitwise_and(img, img, mask=mask)
        x0 = max(cx_px - r_px, 0)
        y0 = max(cy_px - r_px, 0)
        x1 = min(cx_px + r_px, w)
        y1 = min(cy_px + r_px, h)
        recorte = roi[y0:y1, x0:x1]
        #
        if recorte.size == 0 or recorte.shape[0] < 5 or recorte.shape[1] < 5:
            messagebox.showwarning("Advertencia", "El patrón extraído es demasiado pequeño o inválido.")
            return
        # Verificar y establecer ValorConversion
        if not hasattr(self, "ValorConversion") or self.ValorConversion <= 0:
            self.ValorConversion = 1.0
        #
        self.patron_intensidad_referencia = recorte.copy()
        self.radio_referencia_manual = r * self.ValorConversion
        #
        self.btn_marcar.config(relief=tk.RAISED, state=tk.NORMAL, bg="lightgray")
        self.btn_buscar.config(state=tk.NORMAL)
        # --- NUEVO: estimar parámetros desde patrón y aplicar ---
        params = self.estimar_parametros_por_patron(tolerancia_porcentual=0.15)
        if params:
            min_radius = params["min_radius"]
            max_radius = params["max_radius"]
            min_dist = params["min_dist"]
            param1 = params["param1"]
            param2 = params["param2"]
            # Convertir a pixeles (doble diámetro)
            self.min_radius_slider.set(min_radius * 2)
            self.max_radius_slider.set(max_radius * 2)
            self.min_dist_slider.set(min_dist)
            self.param1_slider.set(param1)
            self.param2_slider.set(param2)
            #
            self.update_min_radius(min_radius * 2)
            self.update_max_radius(max_radius * 2)
            self.update_min_dist(min_dist)
            self.update_param1(param1)
            self.update_param2(param2)
            #
            self.selected_shape.set("Círculos")
            self.apply_parameters(min_dist, param1, param2, min_radius * 2, max_radius * 2)
            self.count_contours()

    #                                                               #
    #                                                               #
    ##########################################################################################
    ##########################################################################################
    #****************************************************************************************#
    ##################             Funciones de la estadística           #####################
    ###################                     de los datos                 #####################
    #****************************************************************************************#
    ##########################################################################################
    ##########################################################################################
    #                                                               #
    # Función para calcular estadísticas y actualizar histograma ---#
    def calculate_statistics(self, values):                         #       
        if not values:                                              #
            tk.messagebox.showwarning("Advertencia", "No hay valores en la tabla para calcular estadísticas.")
            return                                                  #
        try:                                                        #
            stats = { # Calcular estadísticas                       #
                    "Cantidad": len(values),                        # Cantidad de valores
                    "Promedio": mean(values),                       # Promedio    
                    "Mediana": median(values),                      # Mediana
                    "Desviación Estándar": stdev(values) if len(values) > 1 else 0, # Desviación estándar
                    "Mínimo": min(values),                          # Minimo valor en la lista
                    "Máximo": max(values),                          # Maximo valor en la lista
            }                                                       #
            # Limpiar estadísticas previas                          #
            for widget in self.stats_frame.winfo_children():        # Limpiar el frame
                widget.destroy()                                    # Limpiar el frame de estadísticas
            # Mostrar estadísticas en el frame                      #     
            for key, value in stats.items():                        # Iterar sobre las estadísticas
                tk.Label(self.stats_frame, text=f"{key}: {value:.2f}", font=("Arial", 9), anchor="w", bg="white")\
                    .pack(fill="x", padx=5)                         # Empaquetar etiquetas en el frame
            # Limpiar gráfico previo del canvas                     #
            for widget in self.hist_canvas.winfo_children():        # Limpiar el canvas     
                widget.destroy()                                    # Limpiar el canvas
            # Generar el histograma                                 #
            fig, ax = plt.subplots(figsize=(4, 2.5), dpi=100)       # Crear figura y ejes
            ax.hist(values, bins='auto', color='red', edgecolor='black', alpha=0.7) # Crear histograma
            ax.set_title("Histograma de Frecuencias")               # Añadir título al gráfico
            ax.set_xlabel("Diámetros")                              # Añadir etiquetas al eje x e y
            ax.set_ylabel("Frecuencia")                             # Añadir etiquetas al eje x e y
            ax.grid(axis='y', alpha=0.75)                           # Añadir cuadrícula al eje y
            fig.tight_layout()                                      # Ajustar el diseño de la figura
            # Convertir gráfico a imagen para el canvas             #
            from matplotlib.backends.backend_tkagg import FigureCanvasTkAgg # Importar el renderizador de canvas 
            canvas = FigureCanvasTkAgg(fig, master=self.hist_canvas)# Convertir figura a canvas
            canvas.draw()                                           # Dibujar canvas       
            canvas_widget = canvas.get_tk_widget()                  # Obtener widget del canvas    
            canvas_widget.pack(fill="both", expand=True)            # Empaquetar el widget en el canvas
        except Exception as e:                                      # Manejo de errores
            tk.messagebox.showerror("Error", f"Error al calcular estadísticas o generar histograma: {e}")   # Mostrar mensaje de error


    # Función para extraer valores de la tabla ---------------------#
    def get_table_values(self):                                     #
        values = []                                                 # Lista para almacenar valores
        for row in self.results_table.get_children():               # Iterar sobre las filas de la tabla
            diameter = self.results_table.item(row, "values")[1]    # Suponiendo que el diámetro está en la segunda columna
            try:                                                    #
                values.append(float(diameter))                      # Convertir a flotante y añadir a la lista
            except ValueError:                                      #
                continue                                            #
        return values                                               # Devolver la lista de valores
    #                                                               #
    ##########################################################################################
    ##########################################################################################
    #****************************************************************************************#
    ##################             Funciones de visualización            #####################
    ###################            de imágenes en las ventana            #####################
    #****************************************************************************************#
    ##########################################################################################
    ##########################################################################################
    #
    # Función para calcular las coordenadas para centrar una imagen ----#
    def calculate_centered_coordinates(self, img_width, img_height):
        canvas_width = self.canvas.winfo_width()
        canvas_height = self.canvas.winfo_height()
        x = max((canvas_width - img_width) // 2, 0)
        y = max((canvas_height - img_height) // 2, 0)
        return x, y

    # Función para actualizar la imagen en el canvas redimensionada y centrada -------------#
    def update_canvas_image(self):
        if self.temp_image is None:
            return
        # Redimensionar la imagen temporal
        img_width, img_height = self.temp_image.size
        scale = self.scale_factor
        new_size = (int(img_width*scale), int(img_height*scale))
        img_resized = self.temp_image.resize(new_size, Image.Resampling.LANCZOS)
        # Calcular coordenadas centradas
        self.img_tk = ImageTk.PhotoImage(img_resized)
        self.canvas.delete("all")
        self.canvas.create_image(0, 0, anchor="nw", image=self.img_tk)
        self.canvas.image = self.img_tk
        self.canvas.config(scrollregion=self.canvas.bbox("all"))

    # Función para convertir y mostrar una imagen de OpenCV encanvas#
    def display_cv_image(self, cv_image):
        if cv_image is None or not isinstance(cv_image, np.ndarray):
            return
        # Convertir de OpenCV (BGR) a PIL (RGB)
        rgb_image = cv2.cvtColor(cv_image, cv2.COLOR_BGR2RGB)
        pil_image = Image.fromarray(rgb_image)
        # Redimensionar la imagen según el factor de escala 
        img_width, img_height = pil_image.size
        new_width = int(img_width*self.scale_factor)
        new_height = int(img_height*self.scale_factor)
        resized_img = pil_image.resize((new_width, new_height), Image.Resampling.LANCZOS)
        # Convertir a ImageTk para mostrar en el canvas
        tk_image = ImageTk.PhotoImage(resized_img)
        # Cálculo del centrado
        self.x_offset, self.y_offset = self.calculate_centered_coordinates(new_width, new_height)
        # Actualizar el canvas con la imagen
        self.canvas.delete("all")
        self.canvas.create_image(self.x_offset, self.y_offset, anchor="nw", image=tk_image)
        self.canvas.image = tk_image
        self.canvas.config(scrollregion=self.canvas.bbox("all"))


    # Función para iniciar el arrastre del canvas ----------#
    def start_drag(self, event):                            #
        self.canvas.scan_mark(event.x, event.y)             #
        self.canvas.unbind("<ButtonPress-1>")               #
        self.canvas.unbind("<B1-Motion>")                   #
        self.canvas.unbind("<ButtonRelease-1>")             #
        self.canvas.bind("<ButtonRelease-1>", self.stop_drag) #


    # Función para arrastrar el canvas ---------------------#
    def drag(self, event):                                  #
        dx = event.x - self.last_x                          # Calcular la diferencia de coordenadas
        dy = event.y - self.last_y                          # Calcular la diferencia de coordenadas
        self.canvas.xview_scroll(int(-dx), "units")         # Desplazar el canvas
        self.canvas.yview_scroll(int(-dy), "units")         # Desplazar el canvas  
        self.last_x, self.last_y = event.x, event.y         # Actualizar las coordenadas del último evento


    # Función para detener el arrastre ---------------------#      
    def stop_drag(self, event):                             #     
        self.canvas.bind("<ButtonPress-1>", self.start_drag)#
        self.canvas.bind("<B1-Motion>", self.drag)          #
        self.canvas.unbind("<ButtonRelease-1>")             #


    # Función para detectar el arrastre con el botón del med#
    def on_drag(self, event):                               #
        delta_x = event.x - self.last_x                     # Calcular la diferencia de coordenadas
        delta_y = event.y - self.last_y                     # Calcular la diferencia de coordenadas
        self.canvas.xview_scroll(-delta_x, "units")         # Desplazar el canvas    
        self.canvas.yview_scroll(-delta_y, "units")         # Desplazar el canvas
        self.last_x = event.x                               # Actualizar las coordenadas del último evento
        self.last_y = event.y                               # Actualizar las coordenadas del último evento


    # Función para el desplazamiento con la rueda del mouse
    def on_mouse_wheel(self, event):
        if event.num == 5 or event.delta < 0:
            self.canvas.yview_scroll(1, "units")
        elif event.num == 4 or event.delta > 0:
            self.canvas.yview_scroll(-1, "units")


    # Función para cargar la imagen seleccionada -------------------#                
    def load_image(self, image_path):                               #
        self.current_image = cv2.imread(image_path)                 # Leer la imagen seleccionada
        self.original_image = self.current_image.copy()             # Crear una copia de la imagen original
        # Convertir a RGB y luego a PIL
        img_rgb = cv2.cvtColor(self.current_image, cv2.COLOR_BGR2RGB)
        self.original_image = Image.fromarray(img_rgb)  # ahora es PIL.Image
        # Crear versión temporal como copia
        self.temp_image = self.original_image.copy()
        # Obtener dimensiones de la imagen original
        self.original_width, self.original_height = self.original_image.size
        self.temp_image = self.original_image.copy()                # Crear una copia de la imagen original
        self.temp_image_name = os.path.basename(image_path)         # Obtener el nombre de la imagen
        #                                                           #
        self.show_image_in_canvas(self.original_image, self.canvas) # Mostrar la imagen original en el canvas
        self.show_image_in_canvas(self.temp_image, self.canvas_temp)# Mostrar la imagen temporal en el canvas
        self.display_cv_image(self.current_image)                   # Mostrar la imagen en el canvas    


    # Función para mostrar una imagen en el canvas -----------------#
    def show_image_in_canvas(self, image, canvas):
        if isinstance(image, Image.Image):
            img_pil = image
        else:
            if image.ndim == 3 and image.shape[-1] == 4:
                image = cv2.cvtColor(image, cv2.COLOR_RGBA2RGB)
            elif image.ndim == 2:
                image = cv2.cvtColor(image, cv2.COLOR_GRAY2RGB)
            img_rgb = cv2.cvtColor(image, cv2.COLOR_BGR2RGB)
            img_pil = Image.fromarray(img_rgb)
        # Si estamos mostrando la imagen en canvas_temp (referencia), ajustamos al tamaño del canvas
        if canvas == self.canvas_temp:
            canvas.update_idletasks()
            canvas_width = canvas.winfo_width()
            canvas_height = canvas.winfo_height()
            # Evitar división por cero al cargar muy temprano
            if canvas_width <= 1 or canvas_height <= 1:
                canvas.after(100, lambda: self.show_image_in_canvas(image, canvas))
                return
            # Redimensionar la imagen para que se ajuste al canvas
            scale = min(canvas_width/img_pil.width, canvas_height/img_pil.height)
            new_width = int(img_pil.width*scale)
            new_height = int(img_pil.height*scale)
            img_resized = img_pil.resize((new_width, new_height), Image.Resampling.LANCZOS)
            # Calcular coordenadas centradas
            x = (canvas_width - new_width) // 2
            y = (canvas_height - new_height) // 2
        else:
            # Para los demás canvas, usar self.scale_factor
            new_width = int(img_pil.width*self.scale_factor)
            new_height = int(img_pil.height*self.scale_factor)
            img_resized = img_pil.resize((new_width, new_height), Image.Resampling.LANCZOS)
            x, y = self.calculate_centered_coordinates(new_width, new_height)
            self.x_offset, self.y_offset = x, y
        # Convertir a ImageTk y mostrar en el canvas
        img_tk = ImageTk.PhotoImage(img_resized)
        canvas.delete("all")
        canvas.create_image(x, y, anchor="nw", image=img_tk)
        canvas.image = img_tk
        canvas.config(scrollregion=canvas.bbox("all"))
        # Activar eventos de zoom solo si no es canvas_temp
        if canvas != self.canvas_temp:
            canvas.bind("<B2-Motion>", self.on_drag)
            canvas.bind("<Button-4>", self.on_mouse_wheel)
            canvas.bind("<Button-5>", self.on_mouse_wheel)
        else:
            canvas.unbind("<B2-Motion>")
            canvas.unbind("<Button-4>")
            canvas.unbind("<Button-5>")


    # Función para limpiar miniaturas
    def clear_thumbnails(self):
        for widget in self.thumbnail_scroll_frame.winfo_children():
            widget.destroy()
        self.image_labels.clear()
        self.image_refs.clear()


    # Función para crear miniatura de una imagen
    def create_thumbnail(self, image_path, size=(90, 90)):
        try:
            # Intentar leer con OpenCV
            img = cv2.imread(image_path, cv2.IMREAD_UNCHANGED)
            if img is None:
                raise ValueError("cv2 no pudo abrir la imagen.")
            # Convertir a RGB si es necesario
            if len(img.shape) == 2:  # escala de grises
                img = cv2.cvtColor(img, cv2.COLOR_GRAY2RGB)
            elif img.shape[2] == 4:  # RGBA
                img = cv2.cvtColor(img, cv2.COLOR_BGRA2RGB)
            else:
                img = cv2.cvtColor(img, cv2.COLOR_BGR2RGB)
        except Exception:
            # Usar PIL como alternativa
            pil_img = Image.open(image_path).convert("RGB")
            img = np.array(pil_img)
        # Redimensionar con PIL y convertir a formato Tkinter
        pil_img = Image.fromarray(img)
        pil_img.thumbnail(size)
        return ImageTk.PhotoImage(pil_img)




    # Función para crear una etiqueta de miniatura
    def create_image_label(self, img_tk, image_path):
        frame = tk.Frame(self.thumbnail_scroll_frame)
        label = tk.Label(frame, image=img_tk)
        label.img_tk = img_tk
        label.bind("<Double-Button-1>", lambda e, path=image_path: self.load_image(path))
        label.pack(side=tk.TOP, padx=5, pady=5, anchor="n")
        name_label = tk.Label(frame, text=os.path.basename(image_path), wraplength=100)
        name_label.pack(side=tk.TOP, anchor="n")
        frame.pack(side=tk.LEFT, padx=5, pady=5, anchor="n")
        self.image_labels.append(label)
        self.image_refs.append(img_tk)


# Función para mostrar las miniaturas de las imágenes en un directorio
    def display_images(self, directory):
        if self.is_loading:
            return
        self.clear_thumbnails()
        self.is_loading = True
        # Buscar archivos de imagen compatibles (incluyendo .tif)
        files = [f for f in os.listdir(directory) if f.lower().endswith(('.png', '.jpg', '.jpeg', '.bmp', '.tif', '.tiff'))]
        for filename in files:
            image_path = os.path.join(directory, filename)
            img_tk = self.create_thumbnail(image_path)
            self.create_image_label(img_tk, image_path)
        self.is_loading = False



    # Función para que se deslice el slider de forma continua
    def start_adjusting(self, slider, delta, callback):
        self.stop_adjusting()
        def repeat():
            self.adjust_slider(slider, delta, callback)
            self.slider_repeat_job = self.after(400, repeat)    #
        repeat()


    # Función para que se ajuste el slider
    def stop_adjusting(self):
        if hasattr(self, "slider_repeat_job") and self.slider_repeat_job:
            self.after_cancel(self.slider_repeat_job)           # 
            self.slider_repeat_job = None


    # Función para ajustar el slider
    def bind_slider_trough(self, slider, callback):
        def on_click(event):
            click_x = event.x
            widget_width = slider.winfo_width()
            min_val = slider.cget("from")
            max_val = slider.cget("to")
            value_range = max_val - min_val
            # Posición actual del thumb (aproximada)
            slider_middle = (slider.get() - min_val)/value_range*widget_width
            delta = +1 if click_x > slider_middle else -1
            self.start_adjusting(slider, delta, callback)
        def on_release(event):
            self.stop_adjusting()
        slider.bind("<ButtonPress-1>", on_click)
        slider.bind("<ButtonRelease-1>", on_release)
    #
    #
    ##########################################################################################
    ##########################################################################################
    #****************************************************************************************#
    ##################             Funciones para la cámara              #####################
    #****************************************************************************************#
    ##########################################################################################
    ##########################################################################################
    #                                                       #
    # Detecta las cámaras disponibles ----------------------#
    def search_cameras(self):                               #
        self.menu.delete(1, tk.END)                         # Limpiar el menú actual
        cameras = self.detect_cameras()                     # Buscar cámaras disponibles
        # Agregar las cámaras encontradas al menú           #
        if not cameras:                                     #
            self.menu.add_command(label="No hay cámaras disponibles", state="disabled")
        else:                                               #
            for index in cameras:                           #
                self.menu.add_command(label=f"Cámara {index}", command=lambda idx=index: self.select_camera(idx))
        # Agregar un separador y la opción de apagar cámara si hay una activa
        if self.camera_active:                              #    
            self.menu.add_separator()                       # 
            self.menu.add_command(label="Apagar cámara", command=self.close_camera)


    # Detecta las cámaras disponibles ----------------------#       
    def detect_cameras(self):                               #
        available_cameras = []                              # Lista para almacenar las cámaras disponibles
        for index in range(10):                             # Probar los primeros 10 índices
            try:
                cap = cv2.VideoCapture(index)               # Usar el backend por defecto en lugar de V4L2
                if cap.isOpened():
                    ret, _ = cap.read()
                    if ret:
                        available_cameras.append(index)     # Agregar la cámara a la lista de disponibles
                cap.release()
            except:
                continue
        return available_cameras


    # Selecciona una cámara y la activa --------------------#
    def select_camera(self, camera_index):                  # Seleccionar una cámara y activarla
        if self.camera_active:                              # Si hay una cámara activa
            self.close_camera()                             # Cerrar la cámara activa
        self.start_camera(camera_index)                     # Iniciar la cámara seleccionada
        self.search_cameras()                               # Actualizar el menú para mostrar la opción de apagar


    # Inicia la cámara seleccionada ------------------------#
    def start_camera(self, camera_index):                   # Iniciar la cámara seleccionada
        try:                                                # Intentar iniciar la cámara
            self.cap = cv2.VideoCapture(camera_index)       # Quitar CV2.CAP_V4L2
            if not self.cap.isOpened():                     #    
                messagebox.showerror("Error", f"No se pudo abrir la cámara {camera_index}")
                return                                      #     
            self.camera_active = True                       # Activar la cámara
            self.toggle_button.config(text=f"Cámara {camera_index} (Activa)")
            self.selected_camera_index = camera_index       # Almacenar el índice de la cámara seleccionada
            self.update_frame()                             # Actualizar el frame de la cámara
        except Exception as e:                              #   
            messagebox.showerror("Error", f"Error al iniciar la cámara: {str(e)}")


    # Actualiza el frame de la cámara ----------------------#
    def update_frame(self):                                 # Actualizar el frame de la cámara
        if self.camera_active and self.cap:                 # Si la cámara está activa y se ha iniciado    
            ret, frame = self.cap.read()                    #    
            if ret:                                         #
                frame = cv2.cvtColor(frame, cv2.COLOR_BGR2RGB)                      # Convertir de BGR a RGB
                frame = cv2.resize(frame, (self.canvas_width, self.canvas_height))  # Redimensionar
                img = Image.fromarray(frame)                # Convertir a formato de imagen
                imgtk = ImageTk.PhotoImage(image=img)       # Convertir a formato de imagen de Tkinter
                self.camera_canvas.create_image(0, 0, anchor="nw", image=imgtk)     # Mostrar la imagen en el canvas
                self.camera_canvas.image = imgtk            # Almacenar la imagen en el canvas
                self.after(10, self.update_frame)           # Actualizar el frame cada 10 milisegundos


    # Cierra la cámara activa ------------------------------#
    def close_camera(self):                                 # Cerrar la cámara activa
        if self.cap:                                        # Si hay una cámara activa
            self.cap.release()                              # Liberar la cámara
            self.cap = None                                 # 
        self.camera_active = False                          # Desactivar la cámara
        self.camera_canvas.delete("all")                    # Limpiar el canvas
        self.toggle_button.config(text="Cámara")            # Actualizar el texto del botón
        self.search_cameras()                               # Actualizar el menú para mostrar las cámaras disponibles
        messagebox.showinfo("Cámara", "Cámara apagada.") 
    #
    #
    ##########################################################################################
    ##########################################################################################
    #****************************************************************************************#
    ##################           Descripción de las Funciones            #####################
    #****************************************************************************************#
    ##########################################################################################
    ##########################################################################################
    #                                                       #
    #  ----------------------#
    def agregar_tooltip(self, widget, text):
        # Eliminar tooltip anterior si existe
        if hasattr(widget, "_tooltip_window") and widget._tooltip_window is not None:
            widget._tooltip_window.destroy()
            widget._tooltip_window = None
        tooltip = tk.Toplevel(widget)
        tooltip.withdraw()
        tooltip.overrideredirect(True)
        tooltip_label = tk.Label(tooltip, text=text, background="white", relief="solid", borderwidth=1)
        tooltip_label.pack()
        widget._tooltip_window = tooltip
        def show_tooltip(event):
            x = event.x_root + 10
            y = event.y_root + 10
            tooltip.geometry(f"+{x}+{y}")
            tooltip.deiconify()
        def hide_tooltip(event):
            tooltip.withdraw()
        widget.bind("<Enter>", show_tooltip)
        widget.bind("<Leave>", hide_tooltip)
    #
    #
    #
    ##########################################################################################
    ##########################################################################################
    ##########################################################################################
    ##########################################################################################
    #                                           #
    # Función para cerrar la ventana principal  #
    def on_closing(self):                       # Verificar si el usuario desea salir de la aplicación
        if messagebox.askokcancel("Salir", "¿Desea salir de la aplicación?"):
            self.quit()                         # Cerrar la ventana principal
            self.destroy()                      # Destruir la ventana principal
            os._exit(0)                         # Forzar la terminación del proceso
    #                                           #
    #                                           #
if __name__ == "__main__":                      # Ejecutar la aplicación
    viewer = Ventana_Usuario_v5_05()            # Crear una instancia de la clase
    viewer.mainloop()                           # Método principal para mostrar la ventana