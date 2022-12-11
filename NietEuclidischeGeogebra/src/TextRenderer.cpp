#include "TextRenderer.h"
#include "stb/stb_image.h"

#include "Constants.h"
#include "Util.h"
#include "Application.h"

TextRenderer::TextRenderer(const std::string& fontName)
	: m_TextShader("textShader")
{
	m_TextShader.SetUniform("u_TextImage", 0);
	m_Font = std::make_shared<Font>(fontName);
}

TextRenderer::~TextRenderer()
{
}

void TextRenderer::AddToRenderQueue(const std::shared_ptr<Text>& m_Text)
{
	m_RenderQueue.push(m_Text);
}

void TextRenderer::RenderQueue()
{
	m_TextShader.Bind();
	glActiveTexture(GL_TEXTURE0);
	glBindTexture(GL_TEXTURE_2D, m_Font->GetBitmap());
	while (m_RenderQueue.size() != 0)
	{
		std::shared_ptr<Text> t = m_RenderQueue.front();
		m_RenderQueue.pop();

		glBindVertexArray(t->m_Vao);
		glDrawElements(GL_TRIANGLES, t->m_NumLetters * 6, GL_UNSIGNED_INT, nullptr);
	}
}

Font::Font(const std::string& fontName)
	: m_LineHeight{-1}, m_Size{-1}
{
	std::ifstream file(AssetsFolder + "/fonts/" + fontName + "/info.txt");
	if (!file)
		throw std::runtime_error("Failed to load info for font" + fontName);

	std::string word;
	while (file >> word)
	{
		if (word.compare(0, 5, "face=") == 0)
		{
			m_BaseFont = word.substr(5);
		}
		else if (word.compare(0, 11, "lineHeight=") == 0)
		{
			m_LineHeight = std::atoi(&word[11]);
		}
		else if (word.compare(0, 5, "size=") == 0)
		{
			m_Size = std::atoi(&word[5]);
		}
		else if (word.compare(0, 4, "char") == 0)
		{
			std::string line;
			std::getline(file, line);
			CharacterInfo info;
			int character;
			std::string word;
			std::stringstream lineS;
			lineS << line;
			while (lineS >> word)
			{
				if (word.compare(0, 3, "id=") == 0)
					character = std::atoi(&word[3]);
				else if (word.compare(0, 2, "x=") == 0)
					info.x = std::atoi(&word[2]);
				else if (word.compare(0, 2, "y=") == 0)
					info.y = std::atoi(&word[2]);
				else if (word.compare(0, 6, "width=") == 0)
					info.width = std::atoi(&word[6]);
				else if (word.compare(0, 7, "height=") == 0)
					info.height = std::atoi(&word[7]);
				else if (word.compare(0, 8, "xoffset=") == 0)
					info.xOffset = std::atoi(&word[8]);
				else if (word.compare(0, 8, "yoffset=") == 0)
					info.yOffset = std::atoi(&word[8]);
				else if (word.compare(0, 9, "xadvance=") == 0)
					info.xAdvance = std::atoi(&word[9]);
				else if (word.compare(0, 5, "page=") == 0)
					info.page = std::atoi(&word[5]);
				else if (word.compare(0, 5, "chnl=") == 0)
					info.channel = std::atoi(&word[5]);
			}
			m_CharacterInformation.insert({character, info});
		}
	}

	int width, height, numChannels;
	stbi_set_flip_vertically_on_load(true);
	unsigned char* data{ stbi_load((AssetsFolder + "/fonts/" + fontName + "/bitmap.png").c_str(), &width, &height, &numChannels, 0)};
	if (!data)
		throw std::runtime_error("Failed to load bitmap for font: " + fontName);
	m_TotalHeight = height;
	m_TotalWidth = width;

	GLint imageType;
	switch (numChannels)
	{
	case 1:
		imageType = GL_R;
		break;
	case 2:
		imageType = GL_RG;
		break;
	case 3:
		imageType = GL_RGB;
		break;
	case 4:
		imageType = GL_RGBA;
		break;
	default:
		throw std::runtime_error("Weird number of channels " + std::to_string(numChannels) + " from font " + fontName);
	}
	glGenTextures(1, &m_Bitmap);
	glBindTexture(GL_TEXTURE_2D, m_Bitmap);

	// These first two should really not matter
	glTexParameteri(GL_TEXTURE_2D, GL_TEXTURE_WRAP_S, GL_REPEAT);
	glTexParameteri(GL_TEXTURE_2D, GL_TEXTURE_WRAP_T, GL_REPEAT);

	glTexParameteri(GL_TEXTURE_2D, GL_TEXTURE_MIN_FILTER, GL_NEAREST);
	glTexParameteri(GL_TEXTURE_2D, GL_TEXTURE_MAG_FILTER, GL_NEAREST);
	glTexImage2D(GL_TEXTURE_2D, 0, imageType, width, height, 0, imageType, GL_UNSIGNED_BYTE, data);
	//glGenerateMipmap(GL_TEXTURE_2D);

	stbi_image_free(data);
}

Font::~Font()
{
	glDeleteTextures(1, &m_Bitmap);
}

CharacterInfo Font::GetCharacterInfo(int character)
{
	return m_CharacterInformation.find(character)->second;
}

Text::Text(const std::string& text, float leftX, float rightX, float baseLine, float size)
	: Text(std::vector<int>(text.begin(), text.end()), leftX, rightX, baseLine, size)
{
}

Text::Text(const std::vector<int>& letters, float leftX, float rightX, float baseLine, float size)
	: m_NumLetters{(int)letters.size()}, m_Ib {1<<29}, m_Vb{1<<29}
{
	glGenVertexArrays(1, &m_Vao);
	glBindVertexArray(m_Vao);

	std::array<float,16>* vertexData = new std::array<float,16>[m_NumLetters];
	std::array<unsigned int,6>* indexData = new std::array<unsigned int,6>[m_NumLetters];

	std::shared_ptr<Font> font = Application::Get()->GetRenderer()->GetFont();

	float scale = (float)size / font->GetSize();

	float currentX = leftX;
	for (unsigned int i{ 0 }; i < m_NumLetters; ++i)
	{
		unsigned int begin = i * 4;
		indexData[i] = {
			begin, begin+1, begin+2,
			begin+2, begin+3, begin
		};

		auto[width, height] = Application::Get()->GetWindow()->GetSize();
		const CharacterInfo& info{font->GetCharacterInfo(letters[i])};

		float charLeftX = currentX + (float)info.xOffset / width * scale;
		float charRightX = charLeftX + (float)info.width / width * scale;
		float charBottomY = baseLine;
		if (letters[i] == 'p' || letters[i] == 'q' || letters[i] == 'y' || letters[i] == 'g' || letters[i] == 'j')
			charBottomY -= (float)info.yOffset / height * scale;
		float charTopY = charBottomY + (float)info.height / height * scale;

		float texLeftX = (float)info.x / font->GetWidth();
		float texRightX = texLeftX + (float)info.width / font->GetWidth();
		float texTopY = 1 - ((float)info.y / font->GetHeight());
		float texBottomY = texTopY - (float)info.height / font->GetHeight();

		vertexData[i] = {
			charLeftX,  charBottomY,	texLeftX,  texBottomY,
			charRightX, charBottomY,	texRightX, texBottomY,
			charRightX, charTopY,		texRightX, texTopY,
			charLeftX,  charTopY,		texLeftX,  texTopY
		};

		currentX += ((float)info.xAdvance / width) * scale;
	}
	glGenBuffers(1, &m_Vb);
	glBindBuffer(GL_ARRAY_BUFFER, m_Vb);
	glBufferData(GL_ARRAY_BUFFER, 4 * 4 * m_NumLetters * sizeof(float), vertexData, GL_STATIC_DRAW);

	glEnableVertexAttribArray(0);
	glVertexAttribPointer(0, 2, GL_FLOAT, GL_FALSE, 4 * sizeof(float), 0);
	glEnableVertexAttribArray(1);
	glVertexAttribPointer(1, 2, GL_FLOAT, GL_FALSE, 4 * sizeof(float), (void*)(2*sizeof(float)));

	glGenBuffers(1, &m_Ib);
	glBindBuffer(GL_ELEMENT_ARRAY_BUFFER, m_Ib);
	glBufferData(GL_ELEMENT_ARRAY_BUFFER, 6 * m_NumLetters * sizeof(unsigned int), indexData, GL_STATIC_DRAW);

	delete[] vertexData;
	delete[] indexData;
}

Text::~Text()
{
	glDeleteBuffers(1, &m_Vb);
	glDeleteBuffers(1, &m_Ib);
	glDeleteVertexArrays(1, &m_Vao);
}
